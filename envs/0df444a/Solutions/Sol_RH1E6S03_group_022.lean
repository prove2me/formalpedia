-- Prove2me | solution 1 for RH1E6S03.group_022
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T06:13:01.918057+00:00
-- url     : https://prove2.me/submissions/7338080a-dbdd-4a90-a5ff-03349777e8b2

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S03_part_022_0
import Theorems.Thm_RH1E6S03_part_022_1
import Theorems.Thm_RH1E6S03_part_022_2
import Theorems.Thm_RH1E6S03_part_022_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem group_022 : RS5.BandZeros ((17250877819 : ℝ) / 65536) ((17290182765 : ℝ) / 65536) 1016 := by
  have g0 := part_022_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_022_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_022_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_022_3
  exact g3
end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((17250877819 : ℝ) / 65536) ((17290182765 : ℝ) / 65536) 1016 := by
  apply RH1E6S03.group_022 <;> assumption
