-- Prove2me | solution 1 for RH1E6S08.group_059
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T06:59:47.122537+00:00
-- url     : https://prove2.me/submissions/3f6f7eb6-146c-41de-b9b4-290f767a2007

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S08_part_059_0
import Theorems.Thm_RH1E6S08_part_059_1
import Theorems.Thm_RH1E6S08_part_059_2
import Theorems.Thm_RH1E6S08_part_059_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem group_059 : RS5.BandZeros ((34949108725 : ℝ) / 65536) ((34985975981 : ℝ) / 65536) 1016 := by
  have g0 := part_059_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_059_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_059_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_059_3
  exact g3
end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((34949108725 : ℝ) / 65536) ((34985975981 : ℝ) / 65536) 1016 := by
  apply RH1E6S08.group_059 <;> assumption
