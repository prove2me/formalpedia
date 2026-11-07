-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.segmentPoint_nearest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:44:05.152867+00:00
-- url     : https://prove2.me/submissions/472a2a7c-fc45-4d77-8544-7a287bd822d9

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SegmentProjection
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_clampUnit_quadratic_min
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_segment_distance_sq
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_barycenterMap_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.barycenterMap_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (a b z : Space) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    dist z (segmentPoint a b z) ≤ dist z (a+t • (b-a)) := by
  by_cases hba : b-a = 0
  · simp [segmentPoint,hba]
  · have hQ : 0 < ‖b-a‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hba)
    have hmin := clampUnit_quadratic_min (D := inner ℝ (z-a) (b-a)) hQ ht0 ht1
    have hsq : ‖z-segmentPoint a b z‖^2 ≤ ‖z-(a+t • (b-a))‖^2 := by
      unfold segmentPoint
      rw [segment_distance_sq a b z (segmentParameter a b z),segment_distance_sq a b z t]
      change ‖z-a‖^2-2*clampUnit (inner ℝ (z-a) (b-a)/‖b-a‖^2)*
        inner ℝ (z-a) (b-a)+(clampUnit (inner ℝ (z-a) (b-a)/‖b-a‖^2))^2*‖b-a‖^2 ≤ _
      nlinarith
    rw [dist_eq_norm,dist_eq_norm]
    nlinarith [norm_nonneg (z-segmentPoint a b z),norm_nonneg (z-(a+t • (b-a)))]
end QEC.Coding.BDL26RandomPerturbation
