-- Prove2me | solution 1 for RH1E6S06.group_087
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T22:57:34.892315+00:00
-- url     : https://prove2.me/submissions/0ebf7945-a9aa-47ef-b99a-7be4ee0287a4

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S06_part_087_0
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem group_087 : RS5.BandZeros ((29487183571 : ℝ) / 65536) ((29491200000 : ℝ) / 65536) 109 := by
  exact part_087_0
end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((29487183571 : ℝ) / 65536) ((29491200000 : ℝ) / 65536) 109 := by
  apply RH1E6S06.group_087 <;> assumption
