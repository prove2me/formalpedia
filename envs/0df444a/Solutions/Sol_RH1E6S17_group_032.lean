-- Prove2me | solution 1 for RH1E6S17.group_032
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T21:48:03.965868+00:00
-- url     : https://prove2.me/submissions/a80172c7-3d8d-4e3b-8407-c8ff3646b9f3

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S17_part_032_0
import Theorems.Thm_RH1E6S17_part_032_1
import Theorems.Thm_RH1E6S17_part_032_2
import Theorems.Thm_RH1E6S17_part_032_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem group_032 : RS5.BandZeros ((63380879215 : ℝ) / 65536) ((63415922128 : ℝ) / 65536) 1016 := by
  have g0 := part_032_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_032_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_032_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_032_3
  exact g3
end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((63380879215 : ℝ) / 65536) ((63415922128 : ℝ) / 65536) 1016 := by
  apply RH1E6S17.group_032 <;> assumption
