-- Prove2me | solution 1 for RH1E6S02.group_051
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T04:06:06.745279+00:00
-- url     : https://prove2.me/submissions/09b4f4e7-540c-44a8-8a4e-11ebfe3157c5

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S02_part_051_0
import Theorems.Thm_RH1E6S02_part_051_1
import Theorems.Thm_RH1E6S02_part_051_2
import Theorems.Thm_RH1E6S02_part_051_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem group_051 : RS5.BandZeros ((15150480448 : ℝ) / 65536) ((15190253793 : ℝ) / 65536) 1016 := by
  have g0 := part_051_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_051_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_051_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_051_3
  exact g3
end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((15150480448 : ℝ) / 65536) ((15190253793 : ℝ) / 65536) 1016 := by
  apply RH1E6S02.group_051 <;> assumption
