-- Prove2me | solution 1 for RH1E6S17.part_049_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T22:22:43.148802+00:00
-- url     : https://prove2.me/submissions/b56a98b3-bb01-45c0-9de9-156c83d2cde8

import Definitions.Def_RH1E6S17_D049_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0392 : RS5.BandZeros ((63976096228 : ℝ) / 65536) ((63980488327 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0392.s0 RH1E6S17_0392.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0392.s0 RH1E6S17_0392.rest = RH1E6S17_0392.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0392.s0 :: RH1E6S17_0392.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0392.s0.t = ((63976096228 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0392.s0]
  have e1 : RH1E6S17_0392.sL.t = ((63980488327 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0392.sL]
  rw [e0, e1] at h
  exact h

theorem band_0393 : RS5.BandZeros ((63980488327 : ℝ) / 65536) ((63984863176 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0393.s0 RH1E6S17_0393.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0393.s0 RH1E6S17_0393.rest = RH1E6S17_0393.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0393.s0 :: RH1E6S17_0393.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0393.s0.t = ((63980488327 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0393.s0]
  have e1 : RH1E6S17_0393.sL.t = ((63984863176 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0393.sL]
  rw [e0, e1] at h
  exact h

theorem part_049_0 : RS5.BandZeros ((63976096228 : ℝ) / 65536) ((63984863176 : ℝ) / 65536) 254 := by
  have g0 := band_0392
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0393
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((63976096228 : ℝ) / 65536) ((63984863176 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_049_0 <;> assumption
