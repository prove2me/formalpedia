-- Prove2me | solution 1 for RH1E6S12.group_009
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T08:05:35.83298+00:00
-- url     : https://prove2.me/submissions/eb1aa5dc-fa6d-46c2-9a01-a5da4be634f7

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S12_part_009_0
import Theorems.Thm_RH1E6S12_part_009_1
import Theorems.Thm_RH1E6S12_part_009_2
import Theorems.Thm_RH1E6S12_part_009_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem group_009 : RS5.BandZeros ((46199117005 : ℝ) / 65536) ((46235099373 : ℝ) / 65536) 1016 := by
  have g0 := part_009_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_009_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_009_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_009_3
  exact g3
end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((46199117005 : ℝ) / 65536) ((46235099373 : ℝ) / 65536) 1016 := by
  apply RH1E6S12.group_009 <;> assumption
