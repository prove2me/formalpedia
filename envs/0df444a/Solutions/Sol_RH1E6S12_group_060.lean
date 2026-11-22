-- Prove2me | solution 1 for RH1E6S12.group_060
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T10:31:35.864158+00:00
-- url     : https://prove2.me/submissions/24d9f8df-ce2d-4c2b-a5d0-a9f2c5b65975

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S12_part_060_0
import Theorems.Thm_RH1E6S12_part_060_1
import Theorems.Thm_RH1E6S12_part_060_2
import Theorems.Thm_RH1E6S12_part_060_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem group_060 : RS5.BandZeros ((48030981851 : ℝ) / 65536) ((48066819428 : ℝ) / 65536) 1016 := by
  have g0 := part_060_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_060_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_060_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_060_3
  exact g3
end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((48030981851 : ℝ) / 65536) ((48066819428 : ℝ) / 65536) 1016 := by
  apply RH1E6S12.group_060 <;> assumption
