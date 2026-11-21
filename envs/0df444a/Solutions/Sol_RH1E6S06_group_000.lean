-- Prove2me | solution 1 for RH1E6S06.group_000
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T17:22:37.926156+00:00
-- url     : https://prove2.me/submissions/666b47ff-c95a-4d02-bc79-c487534526b0

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S06_part_000_0
import Theorems.Thm_RH1E6S06_part_000_1
import Theorems.Thm_RH1E6S06_part_000_2
import Theorems.Thm_RH1E6S06_part_000_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem group_000 : RS5.BandZeros ((26214400000 : ℝ) / 65536) ((26252211653 : ℝ) / 65536) 1016 := by
  have g0 := part_000_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_000_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_000_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_000_3
  exact g3
end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((26214400000 : ℝ) / 65536) ((26252211653 : ℝ) / 65536) 1016 := by
  apply RH1E6S06.group_000 <;> assumption
