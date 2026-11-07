-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.displacement_distance_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:54:31.901277+00:00
-- url     : https://prove2.me/submissions/9ccfef07-d7ae-4cd9-8308-613fb9929585

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Slab
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_SmallCap
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set Metric
open scoped ENNReal
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (R : ℝ) (s v : Sphere) :
    dist (R • (s : Space)) (R • (v : Space)) ^ 2 =
      2 * R^2 * (1 - inner ℝ (v : Space) (s : Space)) := by
  rw [dist_eq_norm, ← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_sub_sq_real]
  simp only [norm_coe, one_pow]
  rw [real_inner_comm (s : Space) (v : Space)]
  ring
end QEC.Coding.ProbabilisticConstruction.SphericalCap
