-- Prove2me | solution 1 for RH1E6S15.group_031
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T09:53:51.078891+00:00
-- url     : https://prove2.me/submissions/e0ff2632-b6d4-4807-8f01-7463a61d5cb1

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S15_part_031_0
import Theorems.Thm_RH1E6S15_part_031_1
import Theorems.Thm_RH1E6S15_part_031_2
import Theorems.Thm_RH1E6S15_part_031_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem group_031 : RS5.BandZeros ((56802359353 : ℝ) / 65536) ((56837683891 : ℝ) / 65536) 1016 := by
  have g0 := part_031_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_031_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_031_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_031_3
  exact g3
end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((56802359353 : ℝ) / 65536) ((56837683891 : ℝ) / 65536) 1016 := by
  apply RH1E6S15.group_031 <;> assumption
