-- Prove2me | solution 1 for RH1E6S16.part_028_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T15:38:52.024895+00:00
-- url     : https://prove2.me/submissions/036f0a0f-c16a-4c42-8521-9148a5c4c1db

import Definitions.Def_RH1E6S16_D028_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0224 : RS5.BandZeros ((59968378265 : ℝ) / 65536) ((59972787828 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0224.s0 RH1E6S16_0224.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0224.s0 RH1E6S16_0224.rest = RH1E6S16_0224.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0224.s0 :: RH1E6S16_0224.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0224.s0.t = ((59968378265 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0224.s0]
  have e1 : RH1E6S16_0224.sL.t = ((59972787828 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0224.sL]
  rw [e0, e1] at h
  exact h

theorem band_0225 : RS5.BandZeros ((59972787828 : ℝ) / 65536) ((59977189362 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0225.s0 RH1E6S16_0225.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0225.s0 RH1E6S16_0225.rest = RH1E6S16_0225.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0225.s0 :: RH1E6S16_0225.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0225.s0.t = ((59972787828 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0225.s0]
  have e1 : RH1E6S16_0225.sL.t = ((59977189362 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0225.sL]
  rw [e0, e1] at h
  exact h

theorem part_028_0 : RS5.BandZeros ((59968378265 : ℝ) / 65536) ((59977189362 : ℝ) / 65536) 254 := by
  have g0 := band_0224
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0225
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((59968378265 : ℝ) / 65536) ((59977189362 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_028_0 <;> assumption
