-- Prove2me | solution 1 for RH1E6S11.group_000
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T03:12:10.512014+00:00
-- url     : https://prove2.me/submissions/9c8ad78e-a871-4c7d-98fc-d35ce7fb54fa

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S11_part_000_0
import Theorems.Thm_RH1E6S11_part_000_1
import Theorems.Thm_RH1E6S11_part_000_2
import Theorems.Thm_RH1E6S11_part_000_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem group_000 : RS5.BandZeros ((42598400000 : ℝ) / 65536) ((42634627367 : ℝ) / 65536) 1016 := by
  have g0 := part_000_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_000_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_000_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_000_3
  exact g3
end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((42598400000 : ℝ) / 65536) ((42634627367 : ℝ) / 65536) 1016 := by
  apply RH1E6S11.group_000 <;> assumption
