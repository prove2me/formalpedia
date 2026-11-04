-- Prove2me | solution 1 for ThreeSumApsp.flag_of_not
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:09:30.778203+00:00
-- url     : https://prove2.me/submissions/7d22d830-c122-4cae-9822-5686ab70c9c9

import Mathlib.Algebra.Order.Ring.Int
import Definitions.Def_Submission_ThreeSumApsp_Util_Flag

set_option autoImplicit false
section
open ThreeSumApsp
namespace ThreeSumApsp
theorem _root_.solution {p : Prop} (h : ¬ p) : flag p = 0 := if_neg h
end ThreeSumApsp
