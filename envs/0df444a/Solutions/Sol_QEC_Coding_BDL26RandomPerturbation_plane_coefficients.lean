-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.plane_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:43:48.416882+00:00
-- url     : https://prove2.me/submissions/8f651820-12ff-4f30-b5f6-d367998120eb

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SegmentProjection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GramProjection

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (b c d : Space) (hdet : gramDet b c ≠ 0) :
    ‖b‖^2*planeU b c d+inner ℝ b c*planeV b c d = inner ℝ d b ∧
      inner ℝ b c*planeU b c d+‖c‖^2*planeV b c d = inner ℝ d c := by
  constructor <;> unfold planeU planeV
  all_goals
    field_simp [hdet]
    unfold gramDet
    ring
end QEC.Coding.BDL26RandomPerturbation
