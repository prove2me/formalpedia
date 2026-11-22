-- Prove2me | solution 1 for SZ.golden_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:53:22.497255+00:00
-- url     : https://prove2.me/submissions/bf2a7709-790f-4683-9e71-2079dca766f3

import Definitions.Def_SZ_Defs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.NormNum.Prime
import Definitions.Def_SZ_GoldenS
section
namespace SZ
open Real
private theorem sqrt_five_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
end SZ
end

set_option autoImplicit false
open SZ
open Real
namespace SZ
theorem _root_.solution : golden ^ 2 = golden + 1 := by
  rw [golden]; nlinarith [sqrt_five_sq]
end SZ
