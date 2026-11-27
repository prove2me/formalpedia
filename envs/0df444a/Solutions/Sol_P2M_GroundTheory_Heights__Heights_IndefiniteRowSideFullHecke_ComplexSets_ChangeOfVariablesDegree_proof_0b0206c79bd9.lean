-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_proof_0b0206c79bd9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:56:18.556461+00:00
-- url     : https://prove2.me/submissions/6e6cd703-3c91-4d85-a670-f64824b5c44c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChangeOfVariablesDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChangeOfVariablesDegreePiola
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChangeOfVariablesDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_integral_comp_sub_mul_det_eq_bf4d64f5b312

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open scoped ContDiff
open MeasureTheory Metric
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace ChangeOfVariablesDegree
theorem _root_.solution : ChangeOfVariablesDegree.Statement := by
  intro n φ hφ hu f hf hfc
  cases n with
  | zero =>
    have hid : φ = id := funext fun x => Subsingleton.elim _ _
    subst hid
    simp only [fderiv_id, id_eq, ContinuousLinearMap.det, ContinuousLinearMap.coe_id,
      LinearMap.det_id, mul_one]
  | succ m =>
    set e : Fin (m + 1) → ℝ := Pi.single 0 1 with he
    obtain ⟨C, hC⟩ := (hφ.continuous.sub continuous_id).bounded_above_of_compact_support hu
    have hC' : ∀ x, ‖φ x - x‖ ≤ C := hC
    obtain ⟨r, hr⟩ := hfc.isCompact.isBounded.subset_closedBall 0
    obtain ⟨ru, hru⟩ := hu.isCompact.isBounded.subset_closedBall 0
    have he1 : ‖e‖ = 1 := by simp [he, Pi.norm_single]
    set R := |r| + |ru| + |C| + 1 with hR
    have hpt : ∀ x, f (φ x - R • e) * (fderiv ℝ φ x).det = f (x - R • e) := by
      intro x
      have hRe : ‖R • e‖ = R := by
        rw [norm_smul, he1, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]
      by_cases hx : x ∈ tsupport fun x => φ x - x
      · have hx' := hru hx
        rw [mem_closedBall_zero_iff] at hx'
        have hf1 : f (φ x - R • e) = 0 := by
          refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
          have h1 := hr hmem
          rw [mem_closedBall_zero_iff] at h1
          have h2 : ‖R • e‖ ≤ ‖φ x - R • e‖ + ‖φ x - x‖ + ‖x‖ := by
            calc ‖R • e‖ = ‖-(φ x - R • e) + (φ x - x) + x‖ := by congr 1; abel
              _ ≤ ‖-(φ x - R • e) + (φ x - x)‖ + ‖x‖ := norm_add_le _ _
              _ ≤ ‖φ x - R • e‖ + ‖φ x - x‖ + ‖x‖ := by
                gcongr; exact (norm_add_le _ _).trans (by rw [norm_neg])
          rw [hRe] at h2
          linarith [hC' x, le_abs_self r, le_abs_self ru, le_abs_self C]
        have hf2 : f (x - R • e) = 0 := by
          refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
          have h1 := hr hmem
          rw [mem_closedBall_zero_iff] at h1
          have h2 : ‖R • e‖ ≤ ‖x - R • e‖ + ‖x‖ := by
            calc ‖R • e‖ = ‖-(x - R • e) + x‖ := by congr 1; abel
              _ ≤ ‖-(x - R • e)‖ + ‖x‖ := norm_add_le _ _
              _ = ‖x - R • e‖ + ‖x‖ := by rw [norm_neg]
          rw [hRe] at h2
          have := abs_nonneg C
          linarith [le_abs_self r, le_abs_self ru]
        rw [hf1, hf2, zero_mul]
      · rw [notMem_tsupport_iff_eventuallyEq] at hx
        have hev : φ =ᶠ[nhds x] id := hx.mono fun y hy => by simpa [sub_eq_zero] using hy
        have hfd : fderiv ℝ φ x = ContinuousLinearMap.id ℝ _ := by
          rw [hev.fderiv_eq, fderiv_id]
        have hφx : φ x = x := hev.self_of_nhds
        rw [hfd, hφx, ContinuousLinearMap.det,
          ContinuousLinearMap.coe_id, LinearMap.det_id, mul_one]
    calc ∫ x, f (φ x) * (fderiv ℝ φ x).det
        = ∫ x, f (φ x - R • e) * (fderiv ℝ φ x).det :=
          (ChangeOfVariablesDegree.integral_comp_sub_mul_det_eq φ hφ hu f hf hfc R).symm
      _ = ∫ x, f (x - R • e) := by simp_rw [hpt]
      _ = ∫ x, f x := integral_sub_right_eq_self f (R • e)
end ChangeOfVariablesDegree
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
