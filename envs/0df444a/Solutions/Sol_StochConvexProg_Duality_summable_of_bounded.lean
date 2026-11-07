-- Prove2me | solution 1 for StochConvexProg.Duality.summable_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T14:40:27.05949+00:00
-- url     : https://prove2.me/submissions/f639422d-7780-4bee-8d72-b60fcca566c0

import Mathlib
import Definitions.Def_StochConvexProg_Duality_Problem

open MeasureTheory

namespace SCPSum

variable {n₁ n₂ : ℕ}

/-- The vertex set of the box `[-B₁,B₁]^{n₁} × [-B₂,B₂]^{n₂}`. -/
def V (B₁ B₂ : ℝ) : Set ((Fin n₁ → ℝ) × (Fin n₂ → ℝ)) :=
  (Set.univ.pi fun _ => ({-B₁, B₁} : Set ℝ)) ×ˢ (Set.univ.pi fun _ => ({-B₂, B₂} : Set ℝ))

theorem V_finite (B₁ B₂ : ℝ) : (V (n₁ := n₁) (n₂ := n₂) B₁ B₂).Finite := by
  unfold V
  refine Set.Finite.prod ?_ ?_ <;>
  exact Set.Finite.pi (fun _ => (Set.finite_singleton _).insert _)

theorem mem_hull {B₁ B₂ : ℝ} {x : (Fin n₁ → ℝ) × (Fin n₂ → ℝ)} (h₁ : ‖x.1‖ ≤ B₁)
    (h₂ : ‖x.2‖ ≤ B₂) : x ∈ convexHull ℝ (V B₁ B₂) := by
  unfold V
  rw [convexHull_prod, convexHull_pi, convexHull_pi]
  have hB₁ : 0 ≤ B₁ := (norm_nonneg _).trans h₁
  have hB₂ : 0 ≤ B₂ := (norm_nonneg _).trans h₂
  refine ⟨fun i _ => ?_, fun i _ => ?_⟩
  · rw [convexHull_pair, segment_eq_Icc (by linarith)]
    have := (norm_le_pi_norm x.1 i).trans h₁
    rw [Real.norm_eq_abs] at this
    exact abs_le.mp this
  · rw [convexHull_pair, segment_eq_Icc (by linarith)]
    have := (norm_le_pi_norm x.2 i).trans h₂
    rw [Real.norm_eq_abs] at this
    exact abs_le.mp this

/-- A convex function on the box is bounded in absolute value by the values at the vertices
and at the origin. -/
theorem abs_le_bound (h : (Fin n₁ → ℝ) × (Fin n₂ → ℝ) → ℝ) (hc : ConvexOn ℝ Set.univ h)
    {B₁ B₂ : ℝ} {x : (Fin n₁ → ℝ) × (Fin n₂ → ℝ)} (h₁ : ‖x.1‖ ≤ B₁) (h₂ : ‖x.2‖ ≤ B₂) :
    |h x| ≤ (∑ v ∈ (V_finite (n₁ := n₁) (n₂ := n₂) B₁ B₂).toFinset, |h v|) + 2 * |h 0| := by
  have up : ∀ z : (Fin n₁ → ℝ) × (Fin n₂ → ℝ), ‖z.1‖ ≤ B₁ → ‖z.2‖ ≤ B₂ →
      h z ≤ ∑ v ∈ (V_finite (n₁ := n₁) (n₂ := n₂) B₁ B₂).toFinset, |h v| := by
    intro z hz₁ hz₂
    obtain ⟨v, hv, hzv⟩ := hc.exists_ge_of_mem_convexHull (Set.subset_univ _) (mem_hull hz₁ hz₂)
    refine hzv.trans ((le_abs_self _).trans ?_)
    exact Finset.single_le_sum (f := fun v => |h v|) (fun _ _ => abs_nonneg _)
      ((Set.Finite.mem_toFinset _).mpr hv)
  have hux := up x h₁ h₂
  have hmx := up (-x) (by simpa using h₁) (by simpa using h₂)
  have hmid : h 0 ≤ (1/2 : ℝ) * h x + (1/2 : ℝ) * h (-x) := by
    have := hc.2 (Set.mem_univ x) (Set.mem_univ (-x)) (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    have e : (1/2 : ℝ) • x + (1/2 : ℝ) • -x = 0 := by
      rw [smul_neg, add_neg_cancel]
    rw [e] at this
    simpa [smul_eq_mul] using this
  have h0 := neg_abs_le (h 0)
  have h0' := abs_nonneg (h 0)
  rw [abs_le]
  constructor <;> linarith

theorem measurable_comp {S : Type*} [MeasurableSpace S]
    (g : S → (Fin n₁ → ℝ) → (Fin n₂ → ℝ) → ℝ)
    (hc : ∀ s, ConvexOn ℝ Set.univ (fun x : (Fin n₁ → ℝ) × (Fin n₂ → ℝ) => g s x.1 x.2))
    (hm : ∀ x₁ x₂, Measurable (fun s => g s x₁ x₂))
    (x₁ : S → Fin n₁ → ℝ) (x₂ : S → Fin n₂ → ℝ) (hx₁ : Measurable x₁) (hx₂ : Measurable x₂) :
    Measurable (fun s => g s (x₁ s) (x₂ s)) := by
  let u : (Fin n₁ → ℝ) × (Fin n₂ → ℝ) → S → ℝ := fun i s => g s i.1 i.2
  have hu : Measurable (Function.uncurry u) := by
    refine measurable_uncurry_of_continuous_of_measurable (fun s => ?_) (fun i => hm i.1 i.2)
    exact continuousOn_univ.mp ((hc s).continuousOn isOpen_univ)
  exact hu.comp ((hx₁.prodMk hx₂).prodMk measurable_id)

end SCPSum

open StochConvexProg.Duality in
theorem solution {S : Type*} [MeasurableSpace S] {σ : Measure S}
    [IsProbabilityMeasure σ] {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂)
    (x₁ : S → Fin n₁ → ℝ) (x₂ : S → Fin n₂ → ℝ)
    (hx₁ : Measurable x₁) (hx₂ : Measurable x₂)
    (hb₁ : ∃ B : ℝ, ∀ s, ‖x₁ s‖ ≤ B) (hb₂ : ∃ B : ℝ, ∀ s, ‖x₂ s‖ ≤ B) :
    Measurable (fun s => pr.f₂₀ s (x₁ s) (x₂ s)) ∧
      Integrable (fun s => pr.f₂₀ s (x₁ s) (x₂ s)) σ ∧
      ∀ i, Measurable (fun s => pr.f₂ i s (x₁ s) (x₂ s)) ∧
        ∃ B : ℝ, ∀ᵐ s ∂σ, |pr.f₂ i s (x₁ s) (x₂ s)| ≤ B := by
  obtain ⟨B₁, hB₁⟩ := hb₁
  obtain ⟨B₂, hB₂⟩ := hb₂
  set T := (SCPSum.V_finite (n₁ := n₁) (n₂ := n₂) B₁ B₂).toFinset
  have hm0 := SCPSum.measurable_comp pr.f₂₀ pr.f₂₀_convex pr.f₂₀_measurable x₁ x₂ hx₁ hx₂
  refine ⟨hm0, ?_, fun i => ⟨SCPSum.measurable_comp (pr.f₂ i) (pr.f₂_convex i)
    (pr.f₂_measurable i) x₁ x₂ hx₁ hx₂, ?_⟩⟩
  · have hG : Integrable (fun s => (∑ v ∈ T, |pr.f₂₀ s v.1 v.2|) + 2 * |pr.f₂₀ s 0 0|) σ := by
      refine Integrable.add ?_ ?_
      · exact integrable_finset_sum _ fun v _ => (pr.f₂₀_integrable v.1 v.2).abs
      · exact ((pr.f₂₀_integrable 0 0).abs).const_mul 2
    refine hG.mono' hm0.aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs]
    exact SCPSum.abs_le_bound (fun x => pr.f₂₀ s x.1 x.2) (pr.f₂₀_convex s)
      (x := (x₁ s, x₂ s)) (hB₁ s) (hB₂ s)
  · choose C hC using pr.f₂_bounded i
    refine ⟨(∑ v ∈ T, C v.1 v.2) + 2 * C 0 0, Filter.Eventually.of_forall fun s => ?_⟩
    refine (SCPSum.abs_le_bound (fun x => pr.f₂ i s x.1 x.2) (pr.f₂_convex i s)
      (x := (x₁ s, x₂ s)) (hB₁ s) (hB₂ s)).trans ?_
    gcongr with v hv
    · exact hC v.1 v.2 s
    · exact hC 0 0 s
