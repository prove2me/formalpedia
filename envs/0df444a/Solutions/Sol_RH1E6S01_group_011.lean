-- Prove2me | solution 1 for RH1E6S01.group_011
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T23:53:44.947541+00:00
-- url     : https://prove2.me/submissions/35757d8f-6d9c-45e9-8ae3-6c03dade6c4b

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S01_part_011_0
import Theorems.Thm_RH1E6S01_part_011_1
import Theorems.Thm_RH1E6S01_part_011_2
import Theorems.Thm_RH1E6S01_part_011_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem group_011 : RS5.BandZeros ((10285875945 : ℝ) / 65536) ((10327184302 : ℝ) / 65536) 1016 := by
  have g0 := part_011_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_011_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_011_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_011_3
  exact g3
end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((10285875945 : ℝ) / 65536) ((10327184302 : ℝ) / 65536) 1016 := by
  apply RH1E6S01.group_011 <;> assumption
