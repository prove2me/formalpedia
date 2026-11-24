-- Prove2me | solution 1 for RH1E6S17.part_093_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T00:44:02.906458+00:00
-- url     : https://prove2.me/submissions/66871ef7-bd13-4760-827d-4260df785621

import Definitions.Def_RH1E6S17_D093_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0748 : RS5.BandZeros ((65532003175 : ℝ) / 65536) ((65536000000 : ℝ) / 65536) 117 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0748.s0 RH1E6S17_0748.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0748.s0 RH1E6S17_0748.rest = RH1E6S17_0748.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0748.s0 :: RH1E6S17_0748.rest) = 117 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0748.s0.t = ((65532003175 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0748.s0]
  have e1 : RH1E6S17_0748.sL.t = ((65536000000 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0748.sL]
  rw [e0, e1] at h
  exact h

theorem part_093_2 : RS5.BandZeros ((65532003175 : ℝ) / 65536) ((65536000000 : ℝ) / 65536) 117 := by
  exact band_0748

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((65532003175 : ℝ) / 65536) ((65536000000 : ℝ) / 65536) 117 := by
  apply RH1E6S17.part_093_2 <;> assumption
