-- Prove2me | solution 1 for RH1E6S01.group_005
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T23:39:32.987982+00:00
-- url     : https://prove2.me/submissions/41e941dd-c70f-4bd0-9bbe-ebe8f5fe0cfb

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S01_part_005_0
import Theorems.Thm_RH1E6S01_part_005_1
import Theorems.Thm_RH1E6S01_part_005_2
import Theorems.Thm_RH1E6S01_part_005_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem group_005 : RS5.BandZeros ((10037678581 : ℝ) / 65536) ((10079096768 : ℝ) / 65536) 1016 := by
  have g0 := part_005_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_005_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_005_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_005_3
  exact g3
end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((10037678581 : ℝ) / 65536) ((10079096768 : ℝ) / 65536) 1016 := by
  apply RH1E6S01.group_005 <;> assumption
