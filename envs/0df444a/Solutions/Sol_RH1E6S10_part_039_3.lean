-- Prove2me | solution 1 for RH1E6S10.part_039_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T23:05:06.784814+00:00
-- url     : https://prove2.me/submissions/8d9b7682-a9ee-4a1c-acdc-3e1c11598904

import Definitions.Def_RH1E6S10_D039_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0318 : RS5.BandZeros ((40769600907 : ℝ) / 65536) ((40774138188 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0318.s0 RH1E6S10_0318.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0318.s0 RH1E6S10_0318.rest = RH1E6S10_0318.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0318.s0 :: RH1E6S10_0318.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0318.s0.t = ((40769600907 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0318.s0]
  have e1 : RH1E6S10_0318.sL.t = ((40774138188 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0318.sL]
  rw [e0, e1] at h
  exact h

theorem band_0319 : RS5.BandZeros ((40774138188 : ℝ) / 65536) ((40778693323 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0319.s0 RH1E6S10_0319.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0319.s0 RH1E6S10_0319.rest = RH1E6S10_0319.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0319.s0 :: RH1E6S10_0319.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0319.s0.t = ((40774138188 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0319.s0]
  have e1 : RH1E6S10_0319.sL.t = ((40778693323 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0319.sL]
  rw [e0, e1] at h
  exact h

theorem part_039_3 : RS5.BandZeros ((40769600907 : ℝ) / 65536) ((40778693323 : ℝ) / 65536) 254 := by
  have g0 := band_0318
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0319
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((40769600907 : ℝ) / 65536) ((40778693323 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_039_3 <;> assumption
