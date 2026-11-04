-- Prove2me | solution 1 for ThreeSumApsp.flag_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:58:50.995808+00:00
-- url     : https://prove2.me/submissions/16fd2c1b-db67-4278-8508-0d48164aa684

import Mathlib.Algebra.Order.Ring.Int
import Definitions.Def_Submission_ThreeSumApsp_Util_Flag
import Theorems.Thm_ThreeSumApsp_flag_of
import Theorems.Thm_ThreeSumApsp_flag_of_not

set_option autoImplicit false
section
open ThreeSumApsp
namespace ThreeSumApsp
theorem _root_.solution {p : Prop} : flag p = 1 ↔ p := by
  by_cases h : p
  · exact iff_of_true (flag_of h) h
  · exact iff_of_false (by rw [flag_of_not h]; decide) h
end ThreeSumApsp
