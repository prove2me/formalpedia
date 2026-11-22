-- Prove2me | solution 1 for RH1E6S10.group_022
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T22:29:03.600966+00:00
-- url     : https://prove2.me/submissions/f706de82-5fb8-4aa1-ad2f-73c6dbf8fa6a

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S10_part_022_0
import Theorems.Thm_RH1E6S10_part_022_1
import Theorems.Thm_RH1E6S10_part_022_2
import Theorems.Thm_RH1E6S10_part_022_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem group_022 : RS5.BandZeros ((40123576838 : ℝ) / 65536) ((40159987027 : ℝ) / 65536) 1016 := by
  have g0 := part_022_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_022_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_022_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_022_3
  exact g3
end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((40123576838 : ℝ) / 65536) ((40159987027 : ℝ) / 65536) 1016 := by
  apply RH1E6S10.group_022 <;> assumption
