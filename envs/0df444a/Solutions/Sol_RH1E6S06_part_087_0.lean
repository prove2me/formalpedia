-- Prove2me | solution 1 for RH1E6S06.part_087_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T22:50:23.401112+00:00
-- url     : https://prove2.me/submissions/842e026b-d0fc-4c43-a3e4-1c1e5e76b00c

import Definitions.Def_RH1E6S06_D087_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0696 : RS5.BandZeros ((29487183571 : ℝ) / 65536) ((29491200000 : ℝ) / 65536) 109 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0696.s0 RH1E6S06_0696.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0696.s0 RH1E6S06_0696.rest = RH1E6S06_0696.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0696.s0 :: RH1E6S06_0696.rest) = 109 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0696.s0.t = ((29487183571 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0696.s0]
  have e1 : RH1E6S06_0696.sL.t = ((29491200000 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0696.sL]
  rw [e0, e1] at h
  exact h

theorem part_087_0 : RS5.BandZeros ((29487183571 : ℝ) / 65536) ((29491200000 : ℝ) / 65536) 109 := by
  exact band_0696

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((29487183571 : ℝ) / 65536) ((29491200000 : ℝ) / 65536) 109 := by
  apply RH1E6S06.part_087_0 <;> assumption
