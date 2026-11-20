-- Prove2me | solution 1 for RH1E6S00.group_032
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T21:58:46.284389+00:00
-- url     : https://prove2.me/submissions/2fdea18a-32e8-4f17-a5a7-55e1036ecf2f

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S00_part_032_0
import Theorems.Thm_RH1E6S00_part_032_1
import Theorems.Thm_RH1E6S00_part_032_2
import Theorems.Thm_RH1E6S00_part_032_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem group_032 : RS5.BandZeros ((7923472272 : ℝ) / 65536) ((7965880653 : ℝ) / 65536) 1016 := by
  have g0 := part_032_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_032_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_032_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_032_3
  exact g3
end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((7923472272 : ℝ) / 65536) ((7965880653 : ℝ) / 65536) 1016 := by
  apply RH1E6S00.group_032 <;> assumption
