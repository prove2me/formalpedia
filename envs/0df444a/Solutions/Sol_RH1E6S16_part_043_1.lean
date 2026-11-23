-- Prove2me | solution 1 for RH1E6S16.part_043_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T16:36:55.94506+00:00
-- url     : https://prove2.me/submissions/7968b370-1105-44a4-a967-134d212e8019

import Definitions.Def_RH1E6S16_D043_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0346 : RS5.BandZeros ((60504816223 : ℝ) / 65536) ((60509233187 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0346.s0 RH1E6S16_0346.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0346.s0 RH1E6S16_0346.rest = RH1E6S16_0346.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0346.s0 :: RH1E6S16_0346.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0346.s0.t = ((60504816223 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0346.s0]
  have e1 : RH1E6S16_0346.sL.t = ((60509233187 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0346.sL]
  rw [e0, e1] at h
  exact h

theorem band_0347 : RS5.BandZeros ((60509233187 : ℝ) / 65536) ((60513604995 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0347.s0 RH1E6S16_0347.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0347.s0 RH1E6S16_0347.rest = RH1E6S16_0347.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0347.s0 :: RH1E6S16_0347.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0347.s0.t = ((60509233187 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0347.s0]
  have e1 : RH1E6S16_0347.sL.t = ((60513604995 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0347.sL]
  rw [e0, e1] at h
  exact h

theorem part_043_1 : RS5.BandZeros ((60504816223 : ℝ) / 65536) ((60513604995 : ℝ) / 65536) 254 := by
  have g0 := band_0346
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0347
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((60504816223 : ℝ) / 65536) ((60513604995 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_043_1 <;> assumption
