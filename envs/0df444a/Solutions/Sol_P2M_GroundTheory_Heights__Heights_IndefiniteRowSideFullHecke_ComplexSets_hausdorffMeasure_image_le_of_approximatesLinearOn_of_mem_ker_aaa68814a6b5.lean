-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hausdorffMeasure_image_le_of_approximatesLinearOn_of_mem_ker_aaa68814a6b5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:31:44.218843+00:00
-- url     : https://prove2.me/submissions/fc7de7cf-fca9-41e3-b300-6b4562a5dab2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCriticalImageNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCriticalImageNull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_shrinkAlong_apply_d4636c48fe45
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_det_shrinkAlong_8034e11a8f81

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {f : (ι → ℝ) → F}
    {A : (ι → ℝ) →L[ℝ] F} {k : ι → ℝ} {i0 : ι} (hk : A k = 0) (hki : k i0 = 1) {δ : ℝ≥0}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {t : Set (ι → ℝ)} (ht : ApproximatesLinearOn f A t δ) :
    μH[Fintype.card ι] (f '' t) ≤
      ((Real.toNNReal (‖A‖ + 1 + ‖k‖) : ℝ≥0∞)) ^ (Fintype.card ι : ℝ) * ENNReal.ofReal δ *
        volume t := by
  have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
  have hδ1' : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  set T := shrinkAlong i0 k (δ : ℝ) with hTdef
  have hT : ∀ z, T z = z - ((1 - (δ : ℝ)) * z i0) • k := shrinkAlong_apply i0 k _
  have hTi : ∀ z, T z i0 = δ * z i0 := by
    intro z; rw [hT]; simp [hki]; ring
  let S : (ι → ℝ) → (ι → ℝ) := fun w => w + (((δ : ℝ)⁻¹ - 1) * w i0) • k
  have hST : ∀ x, S (T x) = x := by
    intro x
    simp only [S, hTi]
    have hδne : (δ : ℝ) ≠ 0 := hδ0'.ne'
    have : ((δ : ℝ)⁻¹ - 1) * (δ * x i0) = (1 - δ) * x i0 := by field_simp
    rw [this, hT, sub_add_cancel]
  have himg : f '' t = (f ∘ S) '' (T '' t) := by
    rw [image_image]; simp [hST]
  have hlip : LipschitzOnWith (Real.toNNReal (‖A‖ + 1 + ‖k‖)) (f ∘ S) (T '' t) := by
    refine LipschitzOnWith.of_dist_le' ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [Function.comp_apply, hST, dist_eq_norm]
    rw [← map_sub]
    set v := x - y with hv
    have hAv : A v = A (T v) := by
      rw [hT, map_sub A v, map_smul, hk, smul_zero, sub_zero]
    have hsplit : (δ : ℝ) • v = (δ : ℝ) • T v + ((1 - δ) * T v i0) • k := by
      rw [hTi, hT]; ext j; simp; ring
    have hδv : (δ : ℝ) * ‖v‖ ≤ ‖T v‖ + ‖T v‖ * ‖k‖ := by
      have h1 : ‖(δ : ℝ) • T v‖ ≤ ‖T v‖ := by
        rw [norm_smul, Real.norm_of_nonneg hδ0'.le]
        exact mul_le_of_le_one_left (norm_nonneg _) hδ1'
      have h2 : ‖((1 - (δ : ℝ)) * T v i0) • k‖ ≤ ‖T v‖ * ‖k‖ := by
        rw [norm_smul, norm_mul, Real.norm_of_nonneg (by linarith)]
        have h3 : ‖T v i0‖ ≤ ‖T v‖ := norm_le_pi_norm _ _
        have h4 : (1 - (δ : ℝ)) * ‖T v i0‖ ≤ ‖T v‖ := by
          calc (1 - (δ : ℝ)) * ‖T v i0‖ ≤ 1 * ‖T v‖ :=
                mul_le_mul (by linarith) h3 (norm_nonneg _) zero_le_one
            _ = ‖T v‖ := one_mul _
        exact mul_le_mul_of_nonneg_right h4 (norm_nonneg _)
      calc (δ : ℝ) * ‖v‖ = ‖(δ : ℝ) • v‖ := by rw [norm_smul, Real.norm_of_nonneg hδ0'.le]
        _ ≤ ‖(δ : ℝ) • T v‖ + ‖((1 - (δ : ℝ)) * T v i0) • k‖ := by
          rw [hsplit]; exact norm_add_le _ _
        _ ≤ ‖T v‖ + ‖T v‖ * ‖k‖ := add_le_add h1 h2
    have happ := ht x hx y hy
    have hAT : ‖A (T v)‖ ≤ ‖A‖ * ‖T v‖ := A.le_opNorm _
    calc ‖f x - f y‖ = ‖(f x - f y - A v) + A v‖ := by rw [sub_add_cancel]
      _ ≤ ‖f x - f y - A v‖ + ‖A v‖ := norm_add_le _ _
      _ ≤ (δ : ℝ) * ‖v‖ + ‖A‖ * ‖T v‖ := by rw [hAv] at happ ⊢; exact add_le_add happ hAT
      _ ≤ (‖A‖ + 1 + ‖k‖) * ‖T v‖ := by nlinarith [hδv]
  rw [himg]
  calc μH[Fintype.card ι] ((f ∘ S) '' (T '' t))
      ≤ ((Real.toNNReal (‖A‖ + 1 + ‖k‖) : ℝ≥0∞)) ^ (Fintype.card ι : ℝ) *
          μH[Fintype.card ι] (T '' t) := hlip.hausdorffMeasure_image_le (by positivity)
    _ = ((Real.toNNReal (‖A‖ + 1 + ‖k‖) : ℝ≥0∞)) ^ (Fintype.card ι : ℝ) *
          (ENNReal.ofReal δ * volume t) := by
      rw [hausdorffMeasure_pi_real, Measure.addHaar_image_linearMap, hTdef, det_shrinkAlong, hki]
      congr 3
      rw [abs_of_pos (by linarith)]
      ring
    _ = _ := by rw [mul_assoc]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
