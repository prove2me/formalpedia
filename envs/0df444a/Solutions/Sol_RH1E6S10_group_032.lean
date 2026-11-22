-- Prove2me | solution 1 for RH1E6S10.group_032
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T22:56:40.482983+00:00
-- url     : https://prove2.me/submissions/79405b84-cff1-4269-95c0-045672c25edb

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S10_part_032_0
import Theorems.Thm_RH1E6S10_part_032_1
import Theorems.Thm_RH1E6S10_part_032_2
import Theorems.Thm_RH1E6S10_part_032_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem group_032 : RS5.BandZeros ((40487630418 : ℝ) / 65536) ((40524020969 : ℝ) / 65536) 1016 := by
  have g0 := part_032_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_032_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_032_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_032_3
  exact g3
end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((40487630418 : ℝ) / 65536) ((40524020969 : ℝ) / 65536) 1016 := by
  apply RH1E6S10.group_032 <;> assumption
