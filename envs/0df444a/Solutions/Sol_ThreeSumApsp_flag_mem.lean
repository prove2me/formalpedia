-- Prove2me | solution 1 for ThreeSumApsp.flag_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:58:53.42513+00:00
-- url     : https://prove2.me/submissions/b8d9dcf8-a42e-4237-988e-613f47183873

import Mathlib.Algebra.Order.Ring.Int
import Definitions.Def_Submission_ThreeSumApsp_Util_Flag
import Theorems.Thm_ThreeSumApsp_flag_of
import Theorems.Thm_ThreeSumApsp_flag_of_not

set_option autoImplicit false
section
open ThreeSumApsp
namespace ThreeSumApsp
theorem _root_.solution (p : Prop) : 0 ≤ flag p ∧ flag p < 2 := by
  by_cases h : p
  · simp [flag_of h]
  · simp [flag_of_not h]
end ThreeSumApsp
