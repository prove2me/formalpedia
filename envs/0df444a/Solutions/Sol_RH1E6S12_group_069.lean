-- Prove2me | solution 1 for RH1E6S12.group_069
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T16:50:04.768198+00:00
-- url     : https://prove2.me/submissions/25722004-ca21-4fd9-a5b2-dd5c4debb0bd

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S12_part_069_0
import Theorems.Thm_RH1E6S12_part_069_1
import Theorems.Thm_RH1E6S12_part_069_2
import Theorems.Thm_RH1E6S12_part_069_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem group_069 : RS5.BandZeros ((48353614254 : ℝ) / 65536) ((48389440989 : ℝ) / 65536) 1016 := by
  have g0 := part_069_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_069_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_069_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_069_3
  exact g3
end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((48353614254 : ℝ) / 65536) ((48389440989 : ℝ) / 65536) 1016 := by
  apply RH1E6S12.group_069 <;> assumption
