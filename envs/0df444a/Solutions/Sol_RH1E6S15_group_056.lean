-- Prove2me | solution 1 for RH1E6S15.group_056
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T11:31:11.657675+00:00
-- url     : https://prove2.me/submissions/c6e00a61-3041-4cd2-8242-bea51d62b6aa

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S15_part_056_0
import Theorems.Thm_RH1E6S15_part_056_1
import Theorems.Thm_RH1E6S15_part_056_2
import Theorems.Thm_RH1E6S15_part_056_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem group_056 : RS5.BandZeros ((57685541258 : ℝ) / 65536) ((57720836344 : ℝ) / 65536) 1016 := by
  have g0 := part_056_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_056_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_056_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_056_3
  exact g3
end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((57685541258 : ℝ) / 65536) ((57720836344 : ℝ) / 65536) 1016 := by
  apply RH1E6S15.group_056 <;> assumption
