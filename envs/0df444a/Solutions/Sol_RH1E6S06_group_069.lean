-- Prove2me | solution 1 for RH1E6S06.group_069
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T22:05:28.606401+00:00
-- url     : https://prove2.me/submissions/7dedd8ff-ff06-4383-9e38-98bf96373499

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S06_part_069_0
import Theorems.Thm_RH1E6S06_part_069_1
import Theorems.Thm_RH1E6S06_part_069_2
import Theorems.Thm_RH1E6S06_part_069_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem group_069 : RS5.BandZeros ((28812863885 : ℝ) / 65536) ((28850360295 : ℝ) / 65536) 1016 := by
  have g0 := part_069_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_069_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_069_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_069_3
  exact g3
end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((28812863885 : ℝ) / 65536) ((28850360295 : ℝ) / 65536) 1016 := by
  apply RH1E6S06.group_069 <;> assumption
