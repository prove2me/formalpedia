-- Prove2me | solution 1 for SZ.silver_conj_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:44:13.46424+00:00
-- url     : https://prove2.me/submissions/f94e0d1b-a665-4450-bf76-b954ef52d4f0

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_SZ_Silver
section
namespace SZ
open Real
private theorem sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
private theorem sqrt_two_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
private theorem one_lt_sqrt_two : 1 < Real.sqrt 2 := by nlinarith [sqrt_two_sq, sqrt_two_pos]
end SZ
end

set_option autoImplicit false
open SZ
open Real
namespace SZ
theorem _root_.solution : (1 : ℝ) - Real.sqrt 2 < 0 := by linarith [one_lt_sqrt_two]
end SZ
