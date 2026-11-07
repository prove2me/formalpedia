-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.gramDet_zero_collinear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:44:39.286676+00:00
-- url     : https://prove2.me/submissions/c490be40-e483-4d3f-8407-5d0b4162020f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SegmentProjection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GramProjection
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_gram_residual_sq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (b c : Space) (hb : b ≠ 0) (hdet : gramDet b c = 0) :
    c = (inner ℝ b c/‖b‖^2) • b := by
  have h := gram_residual_sq b c hb
  rw [hdet] at h
  have hQ : ‖b‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hb)
  have hn := (mul_eq_zero.mp h).resolve_left hQ
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))
end QEC.Coding.BDL26RandomPerturbation
