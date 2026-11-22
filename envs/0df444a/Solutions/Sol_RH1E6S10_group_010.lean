-- Prove2me | solution 1 for RH1E6S10.group_010
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T18:07:09.57792+00:00
-- url     : https://prove2.me/submissions/af3259b5-0997-4791-823d-0dac85fc679b

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S10_part_010_0
import Theorems.Thm_RH1E6S10_part_010_1
import Theorems.Thm_RH1E6S10_part_010_2
import Theorems.Thm_RH1E6S10_part_010_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem group_010 : RS5.BandZeros ((39686321604 : ℝ) / 65536) ((39722775509 : ℝ) / 65536) 1016 := by
  have g0 := part_010_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_010_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_010_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_010_3
  exact g3
end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((39686321604 : ℝ) / 65536) ((39722775509 : ℝ) / 65536) 1016 := by
  apply RH1E6S10.group_010 <;> assumption
