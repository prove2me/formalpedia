-- Prove2me | solution 1 for ProxNewton.Exact.optimal_iff_direction_zero
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:54:49.885745+00:00
-- url     : https://prove2.me/submissions/981664f1-95f5-477c-a8dd-178db0f1d863

import Mathlib
import Definitions.Def_ProxNewton_Exact_Basic

open scoped RealInnerProductSpace Topology
open Filter

namespace ProxNewton.Exact

theorem aux_pnd_deriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (g : E → ℝ) (hg : Differentiable ℝ g) (x d : E) :
    HasDerivAt (fun t : ℝ => g (x + t • d)) ⟪gradient g x, d⟫ 0 := by
  have hline : HasDerivAt (fun t : ℝ => x + t • d) d 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const d).const_add x
  have h2 : HasFDerivAt g (fderiv ℝ g x) (x + (0:ℝ) • d) := by
    simpa using (hg x).hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0:ℝ) hline
  have h4 : fderiv ℝ g x d = ⟪gradient g x, d⟫ := by
    rw [gradient, InnerProductSpace.toDual_symm_apply]
  rw [← h4]
  exact h3

/-- If `ψ` has derivative `c` at `0` and all right difference quotients on `(0,1]`
are `≥ a`, then `a ≤ c`. -/
theorem aux_pnd_ge {ψ : ℝ → ℝ} {c a : ℝ} (hψ : HasDerivAt ψ c 0)
    (hle : ∀ t : ℝ, 0 < t → t ≤ 1 → a ≤ t⁻¹ * (ψ t - ψ 0)) : a ≤ c := by
  have ht := hψ.tendsto_slope_zero_right
  simp only [zero_add, smul_eq_mul] at ht
  apply ge_of_tendsto ht
  have : ∀ᶠ t in 𝓝[>] (0:ℝ), t ∈ Set.Ioo (0:ℝ) 1 := Ioo_mem_nhdsGT (by norm_num)
  filter_upwards [this] with t ht
  exact hle t ht.1 ht.2.le

theorem aux_pnd_le {ψ : ℝ → ℝ} {c a : ℝ} (hψ : HasDerivAt ψ c 0)
    (hle : ∀ t : ℝ, 0 < t → t ≤ 1 → t⁻¹ * (ψ t - ψ 0) ≤ a) : c ≤ a := by
  have ht := hψ.tendsto_slope_zero_right
  simp only [zero_add, smul_eq_mul] at ht
  apply le_of_tendsto ht
  have : ∀ᶠ t in 𝓝[>] (0:ℝ), t ∈ Set.Ioo (0:ℝ) 1 := Ioo_mem_nhdsGT (by norm_num)
  filter_upwards [this] with t ht
  exact hle t ht.1 ht.2.le

end ProxNewton.Exact

open scoped RealInnerProductSpace Topology
open Filter
open ProxNewton.Exact

theorem solution {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (L1 : ℝ)
    (hg : ContDiff ℝ 1 g) (hgc : ConvexOn ℝ Set.univ g) (hL1 : 0 ≤ L1)
    (hgL : ∀ x y : EuclideanSpace ℝ (Fin n), ‖gradient g x - gradient g y‖ ≤ L1 * ‖x - y‖)
    (hD : IsProperClosedConvex D h)
    (x : EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (Δ : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ D) (hH : IsPosDef H) (hΔ : IsSearchDirection g D h x H Δ) :
    IsMinimizer g D h x ↔ Δ = 0 := by
  obtain ⟨_, hDc, hhc, _⟩ := hD
  obtain ⟨hxΔ, hmin⟩ := hΔ
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hpt : ∀ y : EuclideanSpace ℝ (Fin n), ∀ t : ℝ,
      x + t • (y - x) = (1 - t) • x + t • y := by
    intro y t
    rw [smul_sub, sub_smul, one_smul]
    abel
  -- points on the segment
  have hseg : ∀ y ∈ D, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → x + t • (y - x) ∈ D := by
    intro y hy t ht0 ht1
    rw [hpt]
    exact hDc hx hy (sub_nonneg.mpr ht1) ht0 (by ring)
  have hhseg : ∀ y ∈ D, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      h (x + t • (y - x)) ≤ (1 - t) * h x + t * h y := by
    intro y hy t ht0 ht1
    rw [hpt]
    exact hhc.2 hx hy (sub_nonneg.mpr ht1) ht0 (by ring)
  have hgseg : ∀ y : EuclideanSpace ℝ (Fin n), ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      g (x + t • (y - x)) ≤ (1 - t) * g x + t * g y := by
    intro y t ht0 ht1
    rw [hpt]
    exact hgc.2 (Set.mem_univ x) (Set.mem_univ y) (sub_nonneg.mpr ht1) ht0 (by ring)
  constructor
  · rintro ⟨_, hopt⟩
    -- λ ≥ 0
    have hlam : h x - h (x + Δ) ≤ ⟪gradient g x, Δ⟫ := by
      apply aux_pnd_ge (aux_pnd_deriv g hgd x Δ)
      intro t ht0 ht1
      have e : x + Δ - x = Δ := by abel
      have hmem := hseg (x + Δ) hxΔ t ht0.le ht1
      have hh := hhseg (x + Δ) hxΔ t ht0.le ht1
      rw [e] at hmem hh
      have ho := hopt _ hmem
      simp only [zero_smul, add_zero]
      rw [le_inv_mul_iff₀ ht0]
      nlinarith
    have hq := hmin 0 (by simpa using hx)
    simp only [inner_zero_right, map_zero, add_zero, mul_zero] at hq
    by_contra hne
    have hpos := hH.2 Δ hne
    linarith
  · rintro rfl
    refine ⟨hx, fun y hy => ?_⟩
    -- first-order condition for g
    have hg1 : ⟪gradient g x, y - x⟫ ≤ g y - g x := by
      apply aux_pnd_le (aux_pnd_deriv g hgd x (y - x))
      intro t ht0 ht1
      have := hgseg y t ht0.le ht1
      simp only [zero_smul, add_zero]
      rw [inv_mul_le_iff₀ ht0]
      nlinarith
    -- variational inequality for h
    have hq0 : 0 ≤ ⟪H (y - x), y - x⟫ := by
      by_cases hyx : y - x = 0
      · rw [hyx]; simp
      · exact (hH.2 _ hyx).le
    have hh1 : ∀ t : ℝ, 0 < t → t ≤ 1 →
        h x - h y - ⟪gradient g x, y - x⟫ ≤ t * (1 / 2 * ⟪H (y - x), y - x⟫) := by
      intro t ht0 ht1
      have hmem := hseg y hy t ht0.le ht1
      have hh := hhseg y hy t ht0.le ht1
      have hm := hmin (t • (y - x)) hmem
      simp only [inner_zero_right, map_zero, add_zero, mul_zero, zero_add] at hm
      rw [inner_smul_right, map_smul, inner_smul_left, inner_smul_right] at hm
      simp only [RCLike.conj_to_real] at hm
      nlinarith
    have hh2 : h x - h y - ⟪gradient g x, y - x⟫ ≤ 0 := by
      have htend : Tendsto (fun t : ℝ => t * (1 / 2 * ⟪H (y - x), y - x⟫)) (𝓝[>] 0)
          (𝓝 (0 * (1 / 2 * ⟪H (y - x), y - x⟫))) :=
        ((continuous_id.mul continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
      rw [zero_mul] at htend
      apply ge_of_tendsto htend
      have : ∀ᶠ t in 𝓝[>] (0:ℝ), t ∈ Set.Ioo (0:ℝ) 1 := Ioo_mem_nhdsGT (by norm_num)
      filter_upwards [this] with t ht
      exact hh1 t ht.1 ht.2.le
    linarith
