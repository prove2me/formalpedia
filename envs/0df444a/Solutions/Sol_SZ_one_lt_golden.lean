-- Prove2me | solution 1 for SZ.one_lt_golden
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:50:07.785807+00:00
-- url     : https://prove2.me/submissions/1c02aee7-2ce1-41f1-a4bb-ccb0c5fcbae0

import Definitions.Def_SZ_Defs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.NormNum.Prime
import Definitions.Def_SZ_GoldenS
section
namespace SZ
open Real
private theorem sqrt_five_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
private theorem sqrt_five_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
private theorem two_lt_sqrt_five : 2 < Real.sqrt 5 := by
  nlinarith [sqrt_five_sq, sqrt_five_pos]
end SZ
end

set_option autoImplicit false
open SZ
open Real
namespace SZ
theorem _root_.solution : 1 < golden := by
  rw [golden]; linarith [two_lt_sqrt_five]
end SZ
