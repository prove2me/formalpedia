-- Prove2me | solution 1 for RH1E6S03.group_051
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T07:19:21.02245+00:00
-- url     : https://prove2.me/submissions/152aa396-bec6-4c40-8382-c0fe2d4d2ace

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S03_part_051_0
import Theorems.Thm_RH1E6S03_part_051_1
import Theorems.Thm_RH1E6S03_part_051_2
import Theorems.Thm_RH1E6S03_part_051_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem group_051 : RS5.BandZeros ((18387390683 : ℝ) / 65536) ((18426471325 : ℝ) / 65536) 1016 := by
  have g0 := part_051_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_051_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_051_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_051_3
  exact g3
end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((18387390683 : ℝ) / 65536) ((18426471325 : ℝ) / 65536) 1016 := by
  apply RH1E6S03.group_051 <;> assumption
