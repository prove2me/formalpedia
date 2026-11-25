-- Prove2me | solution 1 for PlankProblem.ball_plank_theorem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:18:24.734467+00:00
-- url     : https://prove2.me/submissions/b869a279-d10e-4889-8a01-8ec106ffc07c

module
public import Definitions.Def_BallPlank_ShiftedPlanks
public import Definitions.Def_BallPlank_BallPlankFinal
public import Theorems.Thm_PlankProblem_exists_point_outside_normalized_planks

set_option autoImplicit true
@[expose] public section
public section
open Set
open scoped BigOperators InnerProductSpace Pointwise
noncomputable section
open PlankProblem
variable {n : ℕ}
local notation "Rn" => EuclideanSpace ℝ (Fin n)
namespace PlankProblem
theorem _root_.solution
    {m : ℕ}
    (K : Set Rn)
    (hK : IsConvexBody K)
    (hsymm : IsCentrallySymmetric K)
    (P : Fin m → Plank n)
    (hcover : K ⊆ ⋃ i, (P i : Set Rn)) :
    1 ≤ ∑ i, relativeWidth K (P i) := by
  classical
  obtain ⟨c0, hc0⟩ := hsymm
  obtain ⟨hKc, hKconv, p, hp⟩ := hK
  set K0 : Set Rn := {x | c0 + x ∈ K} with hK0
  have hK0conv : Convex ℝ K0 := by
    intro a ha b hb α β hα hβ hab
    have := hKconv ha hb hα hβ hab
    show c0 + (α • a + β • b) ∈ K
    convert this using 1
    calc c0 + (α • a + β • b) = (α + β) • c0 + (α • a + β • b) := by rw [hab, one_smul]
      _ = α • (c0 + a) + β • (c0 + b) := by module
  have hK0neg : ∀ x ∈ K0, -x ∈ K0 := by
    intro x hx
    have := (hc0 _).mp hx
    show c0 + -x ∈ K
    convert this using 1
    module
  have hpK : p ∈ K := interior_subset hp
  have hq : p - c0 ∈ K0 := by show c0 + (p - c0) ∈ K; simpa using hpK
  have hK00 : (0 : Rn) ∈ K0 := by
    have := hK0conv hq (hK0neg _ hq) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    convert this using 1
    module
  have hK0c : IsCompact K0 := (Homeomorph.addLeft c0).isCompact_preimage.mpr hKc
  obtain ⟨ε, hε, hball⟩ : ∃ ε > 0, Metric.ball (p - c0) ε ⊆ K0 := by
    obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp)
    refine ⟨ε, hε, fun x hx => hb ?_⟩
    show c0 + x ∈ Metric.ball p ε
    rw [Metric.mem_ball, dist_eq_norm] at hx ⊢
    convert hx using 2
    abel
  have hsupp : ∀ i, ∃ v ∈ K0, 0 < ⟪v, (P i).normal⟫_ℝ ∧
      ∀ k ∈ K0, |⟪k, (P i).normal⟫_ℝ| ≤ ⟪v, (P i).normal⟫_ℝ := by
    intro i
    set u := (P i).normal
    obtain ⟨v, hv, hmax⟩ := hK0c.exists_isMaxOn ⟨0, hK00⟩
      (f := fun x : Rn => ⟪x, u⟫_ℝ) (by fun_prop : Continuous fun x : Rn => ⟪x, u⟫_ℝ).continuousOn
    have habs : ∀ k ∈ K0, |⟪k, u⟫_ℝ| ≤ ⟪v, u⟫_ℝ := by
      intro k hk
      have h1 : ⟪k, u⟫_ℝ ≤ ⟪v, u⟫_ℝ := hmax hk
      have h2 : ⟪-k, u⟫_ℝ ≤ ⟪v, u⟫_ℝ := hmax (hK0neg k hk)
      rw [inner_neg_left] at h2
      exact abs_le.mpr ⟨by linarith, h1⟩
    refine ⟨v, hv, ?_, habs⟩
    have hmem : p - c0 + (ε / 2) • u ∈ K0 := hball (by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, (P i).normal_is_unit,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith)
    have h1 := abs_le.mp (habs _ hmem)
    have h2 := abs_le.mp (habs _ hq)
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      (P i).normal_is_unit] at h1
    norm_num at h1
    linarith [h1.1, h1.2, h2.1, h2.2]
  choose v hvK0 hvpos hvmax using hsupp
  set h : Fin m → ℝ := fun i => ⟪v i, (P i).normal⟫_ℝ with hh
  have hdw : ∀ i, directionalWidth K (P i).normal = 2 * h i := by
    intro i
    set u := (P i).normal
    have hG : IsGreatest ((fun x ↦ ⟪x, u⟫_ℝ) '' K) (⟪c0, u⟫_ℝ + h i) := by
      refine ⟨⟨c0 + v i, hvK0 i, by simp [h, u, inner_add_left]⟩, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      have := (abs_le.mp (hvmax i (x - c0) (show c0 + (x - c0) ∈ K by simpa using hx))).2
      rw [inner_sub_left] at this
      simp only [h]
      linarith
    have hL : IsLeast ((fun x ↦ ⟪x, u⟫_ℝ) '' K) (⟪c0, u⟫_ℝ - h i) := by
      refine ⟨⟨c0 + -v i, hK0neg _ (hvK0 i), by
        simp [h, u, inner_add_left, inner_neg_left, sub_eq_add_neg]⟩, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      have := (abs_le.mp (hvmax i (x - c0) (show c0 + (x - c0) ∈ K by simpa using hx))).1
      rw [inner_sub_left] at this
      simp only [h]
      linarith
    unfold directionalWidth
    rw [hG.csSup_eq, hL.csInf_eq]
    ring
  by_contra hlt
  push Not at hlt
  let φ : Fin m → (Rn →ₗ[ℝ] ℝ) := fun i => (h i)⁻¹ • (innerSL ℝ (P i).normal).toLinearMap
  have hφ : ∀ i x, φ i x = ⟪x, (P i).normal⟫_ℝ / h i := fun i x => by
    simp [φ, real_inner_comm, div_eq_inv_mul]
  obtain ⟨y, hy, hyout⟩ := exists_point_outside_normalized_planks hK0conv hK00 hK0neg φ v hvK0
    (fun i => by rw [hφ]; exact div_self (hvpos i).ne')
    (fun i => ((P i).lower - ⟪c0, (P i).normal⟫_ℝ) / h i)
    (fun i => ((P i).upper - ⟪c0, (P i).normal⟫_ℝ) / h i)
    (fun i => div_le_div_of_nonneg_right (by linarith [(P i).lower_le_upper]) (hvpos i).le)
    (by
      have heq : (∑ i : Fin m, (((P i).upper - ⟪c0, (P i).normal⟫_ℝ) / h i -
          ((P i).lower - ⟪c0, (P i).normal⟫_ℝ) / h i) / 2) = ∑ i, relativeWidth K (P i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have := (hvpos i).ne'
        simp only [relativeWidth, Plank.width, hdw i]
        field_simp
        ring
      rw [heq]
      exact hlt)
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover (show c0 + y ∈ K from hy))
  have hi' : c0 + y ∈ Plank.carrier (P i) := hi
  obtain ⟨hl, hu⟩ := hi'
  rw [inner_add_left] at hl hu
  rcases hyout i with h1 | h1 <;> rw [hφ] at h1
  · rw [div_lt_div_iff_of_pos_right (hvpos i)] at h1; linarith
  · rw [div_lt_div_iff_of_pos_right (hvpos i)] at h1; linarith
end PlankProblem
