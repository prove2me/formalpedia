-- Prove2me | solution 1 for RH1E6S16.part_036_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T16:21:35.219295+00:00
-- url     : https://prove2.me/submissions/50155d43-d85e-4650-8d14-4c242787a196

import Definitions.Def_RH1E6S16_D036_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0288 : RS5.BandZeros ((60249840473 : ℝ) / 65536) ((60254232759 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0288.s0 RH1E6S16_0288.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0288.s0 RH1E6S16_0288.rest = RH1E6S16_0288.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0288.s0 :: RH1E6S16_0288.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0288.s0.t = ((60249840473 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0288.s0]
  have e1 : RH1E6S16_0288.sL.t = ((60254232759 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0288.sL]
  rw [e0, e1] at h
  exact h

theorem band_0289 : RS5.BandZeros ((60254232759 : ℝ) / 65536) ((60258643774 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0289.s0 RH1E6S16_0289.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0289.s0 RH1E6S16_0289.rest = RH1E6S16_0289.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0289.s0 :: RH1E6S16_0289.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0289.s0.t = ((60254232759 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0289.s0]
  have e1 : RH1E6S16_0289.sL.t = ((60258643774 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0289.sL]
  rw [e0, e1] at h
  exact h

theorem part_036_0 : RS5.BandZeros ((60249840473 : ℝ) / 65536) ((60258643774 : ℝ) / 65536) 254 := by
  have g0 := band_0288
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0289
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((60249840473 : ℝ) / 65536) ((60258643774 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_036_0 <;> assumption
