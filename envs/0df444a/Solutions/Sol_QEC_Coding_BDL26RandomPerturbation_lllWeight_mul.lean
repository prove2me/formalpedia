-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.lllWeight_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:45:11.813496+00:00
-- url     : https://prove2.me/submissions/c3012567-6d44-457f-942d-bbc3bbef84dd

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters
import Mathlib.Algebra.Order.Ring.Pow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LLLCriterion

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (D : ℕ) : 2*((D : ℝ)+1)*lllWeight D = 1 := by
  have hd : (D : ℝ)+1 ≠ 0 := by positivity
  unfold lllWeight
  field_simp [hd]
end QEC.Coding.BDL26RandomPerturbation
