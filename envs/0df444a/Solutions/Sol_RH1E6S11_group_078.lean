-- Prove2me | solution 1 for RH1E6S11.group_078
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T06:58:41.612782+00:00
-- url     : https://prove2.me/submissions/37c991ad-1ff6-48a3-9c20-072b6c93bfa2

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S11_part_078_0
import Theorems.Thm_RH1E6S11_part_078_1
import Theorems.Thm_RH1E6S11_part_078_2
import Theorems.Thm_RH1E6S11_part_078_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem group_078 : RS5.BandZeros ((45416585589 : ℝ) / 65536) ((45452616262 : ℝ) / 65536) 1016 := by
  have g0 := part_078_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_078_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_078_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_078_3
  exact g3
end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((45416585589 : ℝ) / 65536) ((45452616262 : ℝ) / 65536) 1016 := by
  apply RH1E6S11.group_078 <;> assumption
