-- Prove2me | solution 1 for RH1E6S09.group_047
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T10:34:14.034438+00:00
-- url     : https://prove2.me/submissions/94263b17-7553-4ede-81c8-5b49e9d8cbcf

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S09_part_047_0
import Theorems.Thm_RH1E6S09_part_047_1
import Theorems.Thm_RH1E6S09_part_047_2
import Theorems.Thm_RH1E6S09_part_047_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem group_047 : RS5.BandZeros ((37769106182 : ℝ) / 65536) ((37805717451 : ℝ) / 65536) 1016 := by
  have g0 := part_047_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_047_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_047_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_047_3
  exact g3
end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((37769106182 : ℝ) / 65536) ((37805717451 : ℝ) / 65536) 1016 := by
  apply RH1E6S09.group_047 <;> assumption
