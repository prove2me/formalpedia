-- Prove2me | solution 1 for RH1E6S01.group_080
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T02:12:59.704183+00:00
-- url     : https://prove2.me/submissions/f874eded-e63e-4002-8cb3-30fa712a2e15

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S01_part_080_0
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem group_080 : RS5.BandZeros ((13101727063 : ℝ) / 65536) ((13107200000 : ℝ) / 65536) 138 := by
  exact part_080_0
end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((13101727063 : ℝ) / 65536) ((13107200000 : ℝ) / 65536) 138 := by
  apply RH1E6S01.group_080 <;> assumption
