-- Prove2me | solution 1 for TrulySubquadratic3SUM.threeSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-06T08:24:06.548981+00:00
-- url     : https://prove2.me/submissions/25f6d0e8-f754-4566-953f-4f42d2881dc9

import Theorems.Thm_ThreeSumApsp_wordRam_theorem_22_second
import Theorems.Thm_ThreeSumApsp_WordRam_SolvedInTime_endStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem solution : EndStatement.ThreeSum.SolvedInTime 1.9992 :=
  ThreeSumApsp.wordRam_theorem_22_second.1.endStatement (by norm_num) (by norm_num)
