-- Prove2me | solution 1 for RH1E6S00.group_023
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T21:40:04.608057+00:00
-- url     : https://prove2.me/submissions/957e936e-dae2-44ae-aa6b-d346459ddabf

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S00_part_023_0
import Theorems.Thm_RH1E6S00_part_023_1
import Theorems.Thm_RH1E6S00_part_023_2
import Theorems.Thm_RH1E6S00_part_023_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem group_023 : RS5.BandZeros ((7540824904 : ℝ) / 65536) ((7583456922 : ℝ) / 65536) 1016 := by
  have g0 := part_023_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_023_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_023_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_023_3
  exact g3
end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((7540824904 : ℝ) / 65536) ((7583456922 : ℝ) / 65536) 1016 := by
  apply RH1E6S00.group_023 <;> assumption
