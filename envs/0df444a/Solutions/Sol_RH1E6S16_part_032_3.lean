-- Prove2me | solution 1 for RH1E6S16.part_032_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T15:57:09.277792+00:00
-- url     : https://prove2.me/submissions/2d585af6-d6d0-4b4c-9751-d51dfffc31bf

import Definitions.Def_RH1E6S16_D032_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0262 : RS5.BandZeros ((60135531670 : ℝ) / 65536) ((60139912006 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0262.s0 RH1E6S16_0262.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0262.s0 RH1E6S16_0262.rest = RH1E6S16_0262.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0262.s0 :: RH1E6S16_0262.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0262.s0.t = ((60135531670 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0262.s0]
  have e1 : RH1E6S16_0262.sL.t = ((60139912006 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0262.sL]
  rw [e0, e1] at h
  exact h

theorem band_0263 : RS5.BandZeros ((60139912006 : ℝ) / 65536) ((60144301290 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0263.s0 RH1E6S16_0263.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0263.s0 RH1E6S16_0263.rest = RH1E6S16_0263.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0263.s0 :: RH1E6S16_0263.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0263.s0.t = ((60139912006 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0263.s0]
  have e1 : RH1E6S16_0263.sL.t = ((60144301290 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0263.sL]
  rw [e0, e1] at h
  exact h

theorem part_032_3 : RS5.BandZeros ((60135531670 : ℝ) / 65536) ((60144301290 : ℝ) / 65536) 254 := by
  have g0 := band_0262
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0263
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((60135531670 : ℝ) / 65536) ((60144301290 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_032_3 <;> assumption
