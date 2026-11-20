-- Prove2me | solution 1 for RH1E6S01.group_016
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T00:00:51.366036+00:00
-- url     : https://prove2.me/submissions/4b7ecc98-6f81-461a-ac4a-9236f9aa9a1b

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S01_part_016_0
import Theorems.Thm_RH1E6S01_part_016_1
import Theorems.Thm_RH1E6S01_part_016_2
import Theorems.Thm_RH1E6S01_part_016_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem group_016 : RS5.BandZeros ((10492265664 : ℝ) / 65536) ((10533503467 : ℝ) / 65536) 1016 := by
  have g0 := part_016_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_016_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_016_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_016_3
  exact g3
end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((10492265664 : ℝ) / 65536) ((10533503467 : ℝ) / 65536) 1016 := by
  apply RH1E6S01.group_016 <;> assumption
