-- Prove2me | solution 1 for RH1E6S13.group_075
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T01:38:47.052291+00:00
-- url     : https://prove2.me/submissions/dbba47a8-348c-4bb0-96a9-cd755d91876d

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S13_part_075_0
import Theorems.Thm_RH1E6S13_part_075_1
import Theorems.Thm_RH1E6S13_part_075_2
import Theorems.Thm_RH1E6S13_part_075_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem group_075 : RS5.BandZeros ((51830005123 : ℝ) / 65536) ((51865630677 : ℝ) / 65536) 1016 := by
  have g0 := part_075_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_075_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_075_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_075_3
  exact g3
end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((51830005123 : ℝ) / 65536) ((51865630677 : ℝ) / 65536) 1016 := by
  apply RH1E6S13.group_075 <;> assumption
