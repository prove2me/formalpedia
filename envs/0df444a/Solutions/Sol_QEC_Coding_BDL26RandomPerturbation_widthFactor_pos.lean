-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.widthFactor_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:38:53.17332+00:00
-- url     : https://prove2.me/submissions/dd136e1c-10ac-4bda-b62d-7a5a1879111d

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_cos_mem_open_unit


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution : 0 < widthFactor := by
  have hpi := Real.two_le_pi
  have hc := (cos_mem_open_unit (θ := (1 : ℝ) / 6) (by norm_num) (by linarith)).2
  exact sub_pos.mpr hc
end QEC.Coding.BDL26RandomPerturbation
