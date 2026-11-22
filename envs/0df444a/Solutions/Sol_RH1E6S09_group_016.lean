-- Prove2me | solution 1 for RH1E6S09.group_016
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T09:06:28.693716+00:00
-- url     : https://prove2.me/submissions/60699a43-a299-4f1d-9623-7d36ef9adb5a

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S09_part_016_0
import Theorems.Thm_RH1E6S09_part_016_1
import Theorems.Thm_RH1E6S09_part_016_2
import Theorems.Thm_RH1E6S09_part_016_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem group_016 : RS5.BandZeros ((36632584703 : ℝ) / 65536) ((36669283571 : ℝ) / 65536) 1016 := by
  have g0 := part_016_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_016_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_016_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_016_3
  exact g3
end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((36632584703 : ℝ) / 65536) ((36669283571 : ℝ) / 65536) 1016 := by
  apply RH1E6S09.group_016 <;> assumption
