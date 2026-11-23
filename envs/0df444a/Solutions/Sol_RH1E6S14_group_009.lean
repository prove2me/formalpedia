-- Prove2me | solution 1 for RH1E6S14.group_009
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T03:12:08.351581+00:00
-- url     : https://prove2.me/submissions/18b7e430-60ed-44ec-9e54-acf30de46608

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S14_part_009_0
import Theorems.Thm_RH1E6S14_part_009_1
import Theorems.Thm_RH1E6S14_part_009_2
import Theorems.Thm_RH1E6S14_part_009_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem group_009 : RS5.BandZeros ((52749055718 : ℝ) / 65536) ((52784613133 : ℝ) / 65536) 1016 := by
  have g0 := part_009_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_009_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_009_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_009_3
  exact g3
end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((52749055718 : ℝ) / 65536) ((52784613133 : ℝ) / 65536) 1016 := by
  apply RH1E6S14.group_009 <;> assumption
