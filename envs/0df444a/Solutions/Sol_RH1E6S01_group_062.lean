-- Prove2me | solution 1 for RH1E6S01.group_062
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T01:37:06.282375+00:00
-- url     : https://prove2.me/submissions/a8c850a1-cf27-4842-b2df-340f4a41c5f0

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S01_part_062_0
import Theorems.Thm_RH1E6S01_part_062_1
import Theorems.Thm_RH1E6S01_part_062_2
import Theorems.Thm_RH1E6S01_part_062_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem group_062 : RS5.BandZeros ((12373406620 : ℝ) / 65536) ((12413966292 : ℝ) / 65536) 1016 := by
  have g0 := part_062_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_062_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_062_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_062_3
  exact g3
end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((12373406620 : ℝ) / 65536) ((12413966292 : ℝ) / 65536) 1016 := by
  apply RH1E6S01.group_062 <;> assumption
