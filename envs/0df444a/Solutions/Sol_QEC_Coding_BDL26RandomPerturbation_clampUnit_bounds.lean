-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.clampUnit_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:43:12.019362+00:00
-- url     : https://prove2.me/submissions/1ebca5d4-e152-4552-88d9-6e37d5b748f0

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SegmentProjection

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (x : ℝ) : 0 ≤ clampUnit x ∧ clampUnit x ≤ 1 := by
  exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
end QEC.Coding.BDL26RandomPerturbation
