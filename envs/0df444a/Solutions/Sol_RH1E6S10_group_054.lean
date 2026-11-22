-- Prove2me | solution 1 for RH1E6S10.group_054
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T01:33:50.587987+00:00
-- url     : https://prove2.me/submissions/1b8579df-3a01-4ba3-9512-ca154135f9ea

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S10_part_054_0
import Theorems.Thm_RH1E6S10_part_054_1
import Theorems.Thm_RH1E6S10_part_054_2
import Theorems.Thm_RH1E6S10_part_054_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem group_054 : RS5.BandZeros ((41287579842 : ℝ) / 65536) ((41323917536 : ℝ) / 65536) 1016 := by
  have g0 := part_054_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_054_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_054_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_054_3
  exact g3
end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((41287579842 : ℝ) / 65536) ((41323917536 : ℝ) / 65536) 1016 := by
  apply RH1E6S10.group_054 <;> assumption
