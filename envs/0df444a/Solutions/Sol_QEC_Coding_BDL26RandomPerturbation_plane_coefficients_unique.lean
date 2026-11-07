-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.plane_coefficients_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:43:55.298955+00:00
-- url     : https://prove2.me/submissions/0dcb73d5-c900-44d4-96f9-e06d3631c0f9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SegmentProjection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GramProjection

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (b c d : Space) (hdet : gramDet b c ≠ 0)
    {u v : ℝ} (hb : ‖b‖^2*u+inner ℝ b c*v = inner ℝ d b)
    (hc : inner ℝ b c*u+‖c‖^2*v = inner ℝ d c) :
    u = planeU b c d ∧ v = planeV b c d := by
  constructor
  · unfold planeU
    apply (eq_div_iff hdet).mpr
    unfold gramDet
    linear_combination ‖c‖^2*hb-inner ℝ b c*hc
  · unfold planeV
    apply (eq_div_iff hdet).mpr
    unfold gramDet
    linear_combination ‖b‖^2*hc-inner ℝ b c*hb
end QEC.Coding.BDL26RandomPerturbation
