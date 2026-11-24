-- Prove2me | solution 1 for RH1E6S17.group_051
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T22:41:47.195366+00:00
-- url     : https://prove2.me/submissions/ad86069e-b330-4968-b43e-20a9599687e2

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S17_part_051_0
import Theorems.Thm_RH1E6S17_part_051_1
import Theorems.Thm_RH1E6S17_part_051_2
import Theorems.Thm_RH1E6S17_part_051_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem group_051 : RS5.BandZeros ((64046091221 : ℝ) / 65536) ((64081086317 : ℝ) / 65536) 1016 := by
  have g0 := part_051_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_051_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_051_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_051_3
  exact g3
end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((64046091221 : ℝ) / 65536) ((64081086317 : ℝ) / 65536) 1016 := by
  apply RH1E6S17.group_051 <;> assumption
