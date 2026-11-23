-- Prove2me | solution 1 for RH1E6S16.part_032_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T15:54:07.951802+00:00
-- url     : https://prove2.me/submissions/4852fd97-9b2f-46ff-b613-f38b6426f290

import Definitions.Def_RH1E6S16_D032_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0256 : RS5.BandZeros ((60109119233 : ℝ) / 65536) ((60113534359 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0256.s0 RH1E6S16_0256.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0256.s0 RH1E6S16_0256.rest = RH1E6S16_0256.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0256.s0 :: RH1E6S16_0256.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0256.s0.t = ((60109119233 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0256.s0]
  have e1 : RH1E6S16_0256.sL.t = ((60113534359 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0256.sL]
  rw [e0, e1] at h
  exact h

theorem band_0257 : RS5.BandZeros ((60113534359 : ℝ) / 65536) ((60117936676 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0257.s0 RH1E6S16_0257.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0257.s0 RH1E6S16_0257.rest = RH1E6S16_0257.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0257.s0 :: RH1E6S16_0257.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0257.s0.t = ((60113534359 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0257.s0]
  have e1 : RH1E6S16_0257.sL.t = ((60117936676 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0257.sL]
  rw [e0, e1] at h
  exact h

theorem part_032_0 : RS5.BandZeros ((60109119233 : ℝ) / 65536) ((60117936676 : ℝ) / 65536) 254 := by
  have g0 := band_0256
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0257
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((60109119233 : ℝ) / 65536) ((60117936676 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_032_0 <;> assumption
