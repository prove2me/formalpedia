-- Prove2me | solution 1 for RH1E6S00.group_077
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T23:27:40.900927+00:00
-- url     : https://prove2.me/submissions/195e1278-2974-4bc5-9f02-7f5b0b5d19d3

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S00_part_077_0
import Theorems.Thm_RH1E6S00_part_077_1
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem group_077 : RS5.BandZeros ((9810743070 : ℝ) / 65536) ((9830400000 : ℝ) / 65536) 481 := by
  have g0 := part_077_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_077_1
  exact g1
end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((9810743070 : ℝ) / 65536) ((9830400000 : ℝ) / 65536) 481 := by
  apply RH1E6S00.group_077 <;> assumption
