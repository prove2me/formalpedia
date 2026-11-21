-- Prove2me | solution 1 for RH1E6S05.group_023
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T13:08:36.866877+00:00
-- url     : https://prove2.me/submissions/b4951c7c-4c2e-4643-b6a8-7441b976818a

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S05_part_023_0
import Theorems.Thm_RH1E6S05_part_023_1
import Theorems.Thm_RH1E6S05_part_023_2
import Theorems.Thm_RH1E6S05_part_023_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem group_023 : RS5.BandZeros ((23816608117 : ℝ) / 65536) ((23854782942 : ℝ) / 65536) 1016 := by
  have g0 := part_023_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_023_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_023_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_023_3
  exact g3
end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((23816608117 : ℝ) / 65536) ((23854782942 : ℝ) / 65536) 1016 := by
  apply RH1E6S05.group_023 <;> assumption
