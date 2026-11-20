-- Prove2me | solution 1 for RH1E6S02.group_082
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T05:21:17.737418+00:00
-- url     : https://prove2.me/submissions/70412ed0-cb8e-491d-9f1d-c4d28d98ad4d

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S02_part_082_0
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem group_082 : RS5.BandZeros ((16379475136 : ℝ) / 65536) ((16384000000 : ℝ) / 65536) 116 := by
  exact part_082_0
end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((16379475136 : ℝ) / 65536) ((16384000000 : ℝ) / 65536) 116 := by
  apply RH1E6S02.group_082 <;> assumption
