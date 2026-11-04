-- Prove2me | solution 1 for ThreeSumApsp.flag_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:09:29.662166+00:00
-- url     : https://prove2.me/submissions/f89054d7-dd51-4f87-837b-e83877516d52

import Mathlib.Algebra.Order.Ring.Int
import Definitions.Def_Submission_ThreeSumApsp_Util_Flag

set_option autoImplicit false
section
open ThreeSumApsp
namespace ThreeSumApsp
theorem _root_.solution {p : Prop} (h : p) : flag p = 1 := if_pos h
end ThreeSumApsp
