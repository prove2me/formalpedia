-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_exists_chartMon_bound_d59f0233b978
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:08:39.062016+00:00
-- url     : https://prove2.me/submissions/edcba643-3705-47ed-bfc2-f80bb8c741f7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSmoothHermConstLine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → Geo.HermLine ι) → ℝ)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
theorem _root_.solution {E : Geo.HermLine ι} (hE : IsSmoothHerm E) {d : K → ℕ}
    (hd : ∀ k, E.a k = d k) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (c : (k : K) → ι k) (z : (Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      ‖∏ k, z ⟨k, c k⟩ ^ d k‖ ≤ M * E.h z := by
  set U : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
  set S : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∑ i, ‖z ⟨k, i⟩‖ ^ 2 = 1}
  have hsq : ∀ (z : (Σ k, ι k) → ℂ) (k : K) (i : ι k),
      ‖z ⟨k, i⟩‖ ^ 2 ≤ ∑ i', ‖z ⟨k, i'⟩‖ ^ 2 := fun z k i ↦
    Finset.single_le_sum (f := fun i' ↦ ‖z ⟨k, i'⟩‖ ^ 2) (fun _ _ ↦ sq_nonneg _)
      (Finset.mem_univ i)
  have hSU : S ⊆ U := by
    intro z hz k
    by_contra h
    push Not at h
    have := hz k
    simp [h] at this
  have hS_le : ∀ z ∈ S, ∀ p, ‖z p‖ ≤ 1 := by
    intro z hz p
    have h1 : ‖z ⟨p.1, p.2⟩‖ ^ 2 ≤ 1 := (hz p.1) ▸ hsq z p.1 p.2
    nlinarith [norm_nonneg (z p)]
  have hSc : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · have : S = ⋂ k, (fun z : (Σ k, ι k) → ℂ ↦ ∑ i, ‖z ⟨k, i⟩‖ ^ 2) ⁻¹' {1} := by
        ext z
        simp [S]
      rw [this]
      exact isClosed_iInter fun k ↦ isClosed_singleton.preimage (by fun_prop)
    · refine (Metric.isBounded_closedBall (x := 0) (r := 1)).subset fun z hz ↦ ?_
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (hS_le z hz)
  have hcont : ContinuousOn (fun z ↦ (E.h z)⁻¹) S :=
    (hE.continuousOn.mono hSU).inv₀ fun z hz ↦ (E.pos z (hSU hz)).ne'
  obtain ⟨M₀, hM₀⟩ := hSc.bddAbove_image hcont
  refine ⟨max M₀ 1, le_max_right _ _, fun c z hz ↦ ?_⟩
  set r : K → ℝ := fun k ↦ Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2)
  have hsum : ∀ k, 0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := by
    intro k
    obtain ⟨i, hi⟩ := hz k
    exact lt_of_lt_of_le (by positivity) (hsq z k i)
  have hr : ∀ k, 0 < r k := fun k ↦ Real.sqrt_pos.mpr (hsum k)
  set t : K → ℂ := fun k ↦ (((r k)⁻¹ : ℝ) : ℂ)
  have hnt : ∀ k, ‖t k‖ = (r k)⁻¹ := fun k ↦ by
    simp [t, abs_of_pos (hr k)]
  have ht : ∀ k, t k ≠ 0 := fun k ↦ by
    rw [← norm_ne_zero_iff, hnt]
    exact (inv_pos.mpr (hr k)).ne'
  set w : (Σ k, ι k) → ℂ := fun p ↦ t p.1 * z p
  have hw : w ∈ S := by
    intro k
    simp only [w, norm_mul, mul_pow, ← Finset.mul_sum, hnt, inv_pow]
    rw [Real.sq_sqrt (hsum k).le]
    exact inv_mul_cancel₀ (hsum k).ne'
  have hEw : E.h w = (∏ k, ‖t k‖ ^ d k) * E.h z := by
    rw [E.smul t z ht]
    congr 1
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [hd k, zpow_natCast]
  have hmon : ‖∏ k, w ⟨k, c k⟩ ^ d k‖ = (∏ k, ‖t k‖ ^ d k) * ‖∏ k, z ⟨k, c k⟩ ^ d k‖ := by
    simp only [w, mul_pow, Finset.prod_mul_distrib, norm_mul, norm_prod, norm_pow]
  have hmon1 : ‖∏ k, w ⟨k, c k⟩ ^ d k‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ ↦ norm_nonneg _) fun k _ ↦ by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (hS_le w hw _)
  have hEw1 : 1 ≤ max M₀ 1 * E.h w := by
    have h1 : (E.h w)⁻¹ ≤ M₀ := hM₀ (Set.mem_image_of_mem _ hw)
    have hpos := E.pos w (hSU hw)
    calc (1 : ℝ) = (E.h w)⁻¹ * E.h w := (inv_mul_cancel₀ hpos.ne').symm
      _ ≤ max M₀ 1 * E.h w := mul_le_mul_of_nonneg_right (h1.trans (le_max_left _ _)) hpos.le
  have hT : 0 < ∏ k, ‖t k‖ ^ d k :=
    Finset.prod_pos fun k _ ↦ pow_pos (norm_pos_iff.mpr (ht k)) _
  have key : (∏ k, ‖t k‖ ^ d k) * ‖∏ k, z ⟨k, c k⟩ ^ d k‖ ≤
      (∏ k, ‖t k‖ ^ d k) * (max M₀ 1 * E.h z) := by
    rw [← hmon]
    calc ‖∏ k, w ⟨k, c k⟩ ^ d k‖ ≤ 1 := hmon1
      _ ≤ max M₀ 1 * E.h w := hEw1
      _ = (∏ k, ‖t k‖ ^ d k) * (max M₀ 1 * E.h z) := by rw [hEw]; ring
  exact le_of_mul_le_mul_left key hT
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
