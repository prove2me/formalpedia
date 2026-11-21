-- Prove2me | solution 1 for RH1E6S05.group_037
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T14:01:32.95122+00:00
-- url     : https://prove2.me/submissions/6d7d1420-8b87-4c71-acc3-3884ea478475

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S05_part_037_0
import Theorems.Thm_RH1E6S05_part_037_1
import Theorems.Thm_RH1E6S05_part_037_2
import Theorems.Thm_RH1E6S05_part_037_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem group_037 : RS5.BandZeros ((24350227338 : ℝ) / 65536) ((24388281924 : ℝ) / 65536) 1016 := by
  have g0 := part_037_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_037_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_037_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_037_3
  exact g3
end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((24350227338 : ℝ) / 65536) ((24388281924 : ℝ) / 65536) 1016 := by
  apply RH1E6S05.group_037 <;> assumption
