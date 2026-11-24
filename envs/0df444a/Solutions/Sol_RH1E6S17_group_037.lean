-- Prove2me | solution 1 for RH1E6S17.group_037
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T21:57:33.216949+00:00
-- url     : https://prove2.me/submissions/807e3ec7-d7e8-4592-9beb-f5a7de6264eb

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S17_part_037_0
import Theorems.Thm_RH1E6S17_part_037_1
import Theorems.Thm_RH1E6S17_part_037_2
import Theorems.Thm_RH1E6S17_part_037_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem group_037 : RS5.BandZeros ((63555982799 : ℝ) / 65536) ((63591009006 : ℝ) / 65536) 1016 := by
  have g0 := part_037_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_037_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_037_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_037_3
  exact g3
end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((63555982799 : ℝ) / 65536) ((63591009006 : ℝ) / 65536) 1016 := by
  apply RH1E6S17.group_037 <;> assumption
