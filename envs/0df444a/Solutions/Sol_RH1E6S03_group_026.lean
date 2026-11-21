-- Prove2me | solution 1 for RH1E6S03.group_026
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T06:20:19.365087+00:00
-- url     : https://prove2.me/submissions/f0631062-6a68-4779-bee9-0318fdc5680a

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S03_part_026_0
import Theorems.Thm_RH1E6S03_part_026_1
import Theorems.Thm_RH1E6S03_part_026_2
import Theorems.Thm_RH1E6S03_part_026_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem group_026 : RS5.BandZeros ((17408047350 : ℝ) / 65536) ((17447328537 : ℝ) / 65536) 1016 := by
  have g0 := part_026_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_026_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_026_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_026_3
  exact g3
end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((17408047350 : ℝ) / 65536) ((17447328537 : ℝ) / 65536) 1016 := by
  apply RH1E6S03.group_026 <;> assumption
