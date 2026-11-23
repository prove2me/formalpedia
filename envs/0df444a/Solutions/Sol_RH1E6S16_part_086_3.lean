-- Prove2me | solution 1 for RH1E6S16.part_086_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T19:09:19.528774+00:00
-- url     : https://prove2.me/submissions/3a2e06a1-cd68-4369-b868-e8229f57faac

import Definitions.Def_RH1E6S16_D086_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0694 : RS5.BandZeros ((62032813699 : ℝ) / 65536) ((62037205265 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0694.s0 RH1E6S16_0694.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0694.s0 RH1E6S16_0694.rest = RH1E6S16_0694.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0694.s0 :: RH1E6S16_0694.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0694.s0.t = ((62032813699 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0694.s0]
  have e1 : RH1E6S16_0694.sL.t = ((62037205265 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0694.sL]
  rw [e0, e1] at h
  exact h

theorem band_0695 : RS5.BandZeros ((62037205265 : ℝ) / 65536) ((62041577739 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0695.s0 RH1E6S16_0695.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0695.s0 RH1E6S16_0695.rest = RH1E6S16_0695.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0695.s0 :: RH1E6S16_0695.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0695.s0.t = ((62037205265 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0695.s0]
  have e1 : RH1E6S16_0695.sL.t = ((62041577739 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0695.sL]
  rw [e0, e1] at h
  exact h

theorem part_086_3 : RS5.BandZeros ((62032813699 : ℝ) / 65536) ((62041577739 : ℝ) / 65536) 254 := by
  have g0 := band_0694
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0695
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((62032813699 : ℝ) / 65536) ((62041577739 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_086_3 <;> assumption
