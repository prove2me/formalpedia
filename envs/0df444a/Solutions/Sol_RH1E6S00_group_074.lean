-- Prove2me | solution 1 for RH1E6S00.group_074
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T23:22:52.20218+00:00
-- url     : https://prove2.me/submissions/381bffc0-2aa9-41fe-8183-1f4a26a111f4

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S00_part_074_0
import Theorems.Thm_RH1E6S00_part_074_1
import Theorems.Thm_RH1E6S00_part_074_2
import Theorems.Thm_RH1E6S00_part_074_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem group_074 : RS5.BandZeros ((9686122739 : ℝ) / 65536) ((9727677032 : ℝ) / 65536) 1016 := by
  have g0 := part_074_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_074_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_074_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_074_3
  exact g3
end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((9686122739 : ℝ) / 65536) ((9727677032 : ℝ) / 65536) 1016 := by
  apply RH1E6S00.group_074 <;> assumption
