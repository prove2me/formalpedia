-- Prove2me | solution 1 for RH1E6S08.group_079
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T07:55:41.985868+00:00
-- url     : https://prove2.me/submissions/2641a852-ac33-4497-9c8b-4bc08c793bc0

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S08_part_079_0
import Theorems.Thm_RH1E6S08_part_079_1
import Theorems.Thm_RH1E6S08_part_079_2
import Theorems.Thm_RH1E6S08_part_079_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem group_079 : RS5.BandZeros ((35685714951 : ℝ) / 65536) ((35722498403 : ℝ) / 65536) 1016 := by
  have g0 := part_079_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_079_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_079_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_079_3
  exact g3
end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((35685714951 : ℝ) / 65536) ((35722498403 : ℝ) / 65536) 1016 := by
  apply RH1E6S08.group_079 <;> assumption
