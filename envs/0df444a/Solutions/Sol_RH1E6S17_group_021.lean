-- Prove2me | solution 1 for RH1E6S17.group_021
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T21:05:49.548813+00:00
-- url     : https://prove2.me/submissions/7e4111e1-bfd9-49ce-bbda-ebb01d5f60b4

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S17_part_021_0
import Theorems.Thm_RH1E6S17_part_021_1
import Theorems.Thm_RH1E6S17_part_021_2
import Theorems.Thm_RH1E6S17_part_021_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem group_021 : RS5.BandZeros ((62995498185 : ℝ) / 65536) ((63030550373 : ℝ) / 65536) 1016 := by
  have g0 := part_021_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_021_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_021_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_021_3
  exact g3
end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((62995498185 : ℝ) / 65536) ((63030550373 : ℝ) / 65536) 1016 := by
  apply RH1E6S17.group_021 <;> assumption
