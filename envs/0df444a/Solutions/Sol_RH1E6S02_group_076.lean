-- Prove2me | solution 1 for RH1E6S02.group_076
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T04:57:14.637564+00:00
-- url     : https://prove2.me/submissions/bd75d457-7019-4bfe-b5b1-719cd3a48aa7

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S02_part_076_0
import Theorems.Thm_RH1E6S02_part_076_1
import Theorems.Thm_RH1E6S02_part_076_2
import Theorems.Thm_RH1E6S02_part_076_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem group_076 : RS5.BandZeros ((16142303017 : ℝ) / 65536) ((16181891806 : ℝ) / 65536) 1016 := by
  have g0 := part_076_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_076_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_076_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_076_3
  exact g3
end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((16142303017 : ℝ) / 65536) ((16181891806 : ℝ) / 65536) 1016 := by
  apply RH1E6S02.group_076 <;> assumption
