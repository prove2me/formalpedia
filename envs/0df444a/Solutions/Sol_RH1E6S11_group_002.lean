-- Prove2me | solution 1 for RH1E6S11.group_002
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T03:17:49.92915+00:00
-- url     : https://prove2.me/submissions/558315d3-e9a8-4692-8b5c-eb21a7a3daff

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S11_part_002_0
import Theorems.Thm_RH1E6S11_part_002_1
import Theorems.Thm_RH1E6S11_part_002_2
import Theorems.Thm_RH1E6S11_part_002_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem group_002 : RS5.BandZeros ((42670855171 : ℝ) / 65536) ((42707082541 : ℝ) / 65536) 1016 := by
  have g0 := part_002_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_002_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_002_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_002_3
  exact g3
end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((42670855171 : ℝ) / 65536) ((42707082541 : ℝ) / 65536) 1016 := by
  apply RH1E6S11.group_002 <;> assumption
