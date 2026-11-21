-- Prove2me | solution 1 for RH1E6S08.part_013_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T04:34:44.778837+00:00
-- url     : https://prove2.me/submissions/80dea343-bb51-4445-924c-cf9425b9e514

import Definitions.Def_RH1E6S08_D013_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0108 : RS5.BandZeros ((33268190858 : ℝ) / 65536) ((33272817191 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0108.s0 RH1E6S08_0108.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0108.s0 RH1E6S08_0108.rest = RH1E6S08_0108.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0108.s0 :: RH1E6S08_0108.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0108.s0.t = ((33268190858 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0108.s0]
  have e1 : RH1E6S08_0108.sL.t = ((33272817191 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0108.sL]
  rw [e0, e1] at h
  exact h

theorem band_0109 : RS5.BandZeros ((33272817191 : ℝ) / 65536) ((33277455977 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0109.s0 RH1E6S08_0109.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0109.s0 RH1E6S08_0109.rest = RH1E6S08_0109.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0109.s0 :: RH1E6S08_0109.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0109.s0.t = ((33272817191 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0109.s0]
  have e1 : RH1E6S08_0109.sL.t = ((33277455977 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0109.sL]
  rw [e0, e1] at h
  exact h

theorem part_013_2 : RS5.BandZeros ((33268190858 : ℝ) / 65536) ((33277455977 : ℝ) / 65536) 254 := by
  have g0 := band_0108
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0109
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((33268190858 : ℝ) / 65536) ((33277455977 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_013_2 <;> assumption
