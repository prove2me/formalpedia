-- Prove2me | solution 1 for RH1E6S15.group_080
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T13:09:03.783776+00:00
-- url     : https://prove2.me/submissions/3cedfd18-03a5-4ab8-a20b-89b2376c5fa0

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S15_part_080_0
import Theorems.Thm_RH1E6S15_part_080_1
import Theorems.Thm_RH1E6S15_part_080_2
import Theorems.Thm_RH1E6S15_part_080_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem group_080 : RS5.BandZeros ((58532333701 : ℝ) / 65536) ((58567571574 : ℝ) / 65536) 1016 := by
  have g0 := part_080_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_080_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_080_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_080_3
  exact g3
end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((58532333701 : ℝ) / 65536) ((58567571574 : ℝ) / 65536) 1016 := by
  apply RH1E6S15.group_080 <;> assumption
