-- Prove2me | solution 1 for RH1E6S08.group_021
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T05:03:02.920269+00:00
-- url     : https://prove2.me/submissions/c51c13c3-3fa6-4ad6-9d8e-a7633cb118c3

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S08_part_021_0
import Theorems.Thm_RH1E6S08_part_021_1
import Theorems.Thm_RH1E6S08_part_021_2
import Theorems.Thm_RH1E6S08_part_021_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem group_021 : RS5.BandZeros ((33545776907 : ℝ) / 65536) ((33582764464 : ℝ) / 65536) 1016 := by
  have g0 := part_021_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_021_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_021_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_021_3
  exact g3
end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((33545776907 : ℝ) / 65536) ((33582764464 : ℝ) / 65536) 1016 := by
  apply RH1E6S08.group_021 <;> assumption
