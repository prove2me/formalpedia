-- Prove2me | solution 1 for RH1E6S06.group_035
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T18:52:03.317091+00:00
-- url     : https://prove2.me/submissions/ee576478-5f1c-470f-b9b0-734e2031b6b8

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S06_part_035_0
import Theorems.Thm_RH1E6S06_part_035_1
import Theorems.Thm_RH1E6S06_part_035_2
import Theorems.Thm_RH1E6S06_part_035_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem group_035 : RS5.BandZeros ((27535223760 : ℝ) / 65536) ((27572863436 : ℝ) / 65536) 1016 := by
  have g0 := part_035_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_035_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_035_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_035_3
  exact g3
end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((27535223760 : ℝ) / 65536) ((27572863436 : ℝ) / 65536) 1016 := by
  apply RH1E6S06.group_035 <;> assumption
