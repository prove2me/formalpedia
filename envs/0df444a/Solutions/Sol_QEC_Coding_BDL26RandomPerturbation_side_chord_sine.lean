-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.side_chord_sine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:50:37.418517+00:00
-- url     : https://prove2.me/submissions/02c6c27a-3598-477e-afa1-043912c35d4f

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution : (1 : ℝ) / 6 ≤ 2 * Real.sin (1 / 6) := by
  have h := Real.sin_gt_sub_cube (x := (1 : ℝ) / 6) (by norm_num)
  linarith
end QEC.Coding.BDL26RandomPerturbation
