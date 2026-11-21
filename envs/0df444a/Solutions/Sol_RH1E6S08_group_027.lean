-- Prove2me | solution 1 for RH1E6S08.group_027
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T05:21:55.660862+00:00
-- url     : https://prove2.me/submissions/66659854-11b4-4d0e-a934-8410b2d69889

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S08_part_027_0
import Theorems.Thm_RH1E6S08_part_027_1
import Theorems.Thm_RH1E6S08_part_027_2
import Theorems.Thm_RH1E6S08_part_027_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem group_027 : RS5.BandZeros ((33767685645 : ℝ) / 65536) ((33804651700 : ℝ) / 65536) 1016 := by
  have g0 := part_027_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_027_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_027_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_027_3
  exact g3
end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((33767685645 : ℝ) / 65536) ((33804651700 : ℝ) / 65536) 1016 := by
  apply RH1E6S08.group_027 <;> assumption
