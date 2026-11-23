-- Prove2me | solution 1 for RH1E6S15.group_087
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T13:41:54.114236+00:00
-- url     : https://prove2.me/submissions/9363a2e5-83d8-48cb-a97c-77a2d306f7ce

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S15_part_087_0
import Theorems.Thm_RH1E6S15_part_087_1
import Theorems.Thm_RH1E6S15_part_087_2
import Theorems.Thm_RH1E6S15_part_087_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem group_087 : RS5.BandZeros ((58779118826 : ℝ) / 65536) ((58814380003 : ℝ) / 65536) 1016 := by
  have g0 := part_087_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_087_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_087_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_087_3
  exact g3
end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((58779118826 : ℝ) / 65536) ((58814380003 : ℝ) / 65536) 1016 := by
  apply RH1E6S15.group_087 <;> assumption
