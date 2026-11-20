-- Prove2me | solution 1 for RH1E6S02.group_015
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T02:46:22.975275+00:00
-- url     : https://prove2.me/submissions/2e72d405-0772-426b-909a-51079db7683a

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S02_part_015_0
import Theorems.Thm_RH1E6S02_part_015_1
import Theorems.Thm_RH1E6S02_part_015_2
import Theorems.Thm_RH1E6S02_part_015_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem group_015 : RS5.BandZeros ((13711161591 : ℝ) / 65536) ((13751312169 : ℝ) / 65536) 1016 := by
  have g0 := part_015_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_015_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_015_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_015_3
  exact g3
end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((13711161591 : ℝ) / 65536) ((13751312169 : ℝ) / 65536) 1016 := by
  apply RH1E6S02.group_015 <;> assumption
