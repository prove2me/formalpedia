-- Prove2me | solution 1 for RH1E6S12.group_077
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T17:15:59.936864+00:00
-- url     : https://prove2.me/submissions/b691b0f6-6a37-4b91-9623-c0054b198521

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S12_part_077_0
import Theorems.Thm_RH1E6S12_part_077_1
import Theorems.Thm_RH1E6S12_part_077_2
import Theorems.Thm_RH1E6S12_part_077_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem group_077 : RS5.BandZeros ((48640235553 : ℝ) / 65536) ((48676080567 : ℝ) / 65536) 1016 := by
  have g0 := part_077_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_077_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_077_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_077_3
  exact g3
end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((48640235553 : ℝ) / 65536) ((48676080567 : ℝ) / 65536) 1016 := by
  apply RH1E6S12.group_077 <;> assumption
