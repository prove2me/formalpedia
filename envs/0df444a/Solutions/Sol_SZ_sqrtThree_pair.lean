-- Prove2me | solution 1 for SZ.sqrtThree_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:46:47.274749+00:00
-- url     : https://prove2.me/submissions/ea5f85c1-10de-48c6-9014-74cb6a1cd04a

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_SZ_QuadThm6
section
namespace SZ
open Real
private theorem sqrt_three_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
private theorem sqrt_three_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
private theorem one_lt_sqrt_three : 1 < Real.sqrt 3 := by
  nlinarith [sqrt_three_sq, sqrt_three_pos]
private theorem sqrt_three_lt_two : Real.sqrt 3 < 2 := by
  nlinarith [sqrt_three_sq, sqrt_three_pos]
end SZ
end

set_option autoImplicit false
open SZ
open Real
namespace SZ
theorem _root_.solution : Pair (1 + Real.sqrt 3) (1 - Real.sqrt 3) 2 2 where
  one_lt := by linarith [sqrt_three_pos]
  absLt := by
    rw [abs_lt]
    constructor <;> [linarith [sqrt_three_lt_two]; linarith [one_lt_sqrt_three]]
  sum := by push_cast; ring
  prod := by push_cast; nlinarith [sqrt_three_sq]
end SZ
