-- Prove2me | solution 1 for RH1E6S11.group_051
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T05:39:00.522664+00:00
-- url     : https://prove2.me/submissions/aad94751-1616-4d2b-8d62-d1cc56c0d9c9

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S11_part_051_0
import Theorems.Thm_RH1E6S11_part_051_1
import Theorems.Thm_RH1E6S11_part_051_2
import Theorems.Thm_RH1E6S11_part_051_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem group_051 : RS5.BandZeros ((44442818626 : ℝ) / 65536) ((44478907769 : ℝ) / 65536) 1016 := by
  have g0 := part_051_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_051_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_051_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_051_3
  exact g3
end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((44442818626 : ℝ) / 65536) ((44478907769 : ℝ) / 65536) 1016 := by
  apply RH1E6S11.group_051 <;> assumption
