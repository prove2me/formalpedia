-- Prove2me | solution 1 for RH1E6S16.part_064_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T17:59:57.569807+00:00
-- url     : https://prove2.me/submissions/8f73c2b0-9cf8-4a5b-9bc0-7dc9efb69122

import Definitions.Def_RH1E6S16_D064_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0518 : RS5.BandZeros ((61260431154 : ℝ) / 65536) ((61264844909 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0518.s0 RH1E6S16_0518.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0518.s0 RH1E6S16_0518.rest = RH1E6S16_0518.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0518.s0 :: RH1E6S16_0518.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0518.s0.t = ((61260431154 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0518.s0]
  have e1 : RH1E6S16_0518.sL.t = ((61264844909 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0518.sL]
  rw [e0, e1] at h
  exact h

theorem band_0519 : RS5.BandZeros ((61264844909 : ℝ) / 65536) ((61269216924 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0519.s0 RH1E6S16_0519.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0519.s0 RH1E6S16_0519.rest = RH1E6S16_0519.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0519.s0 :: RH1E6S16_0519.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0519.s0.t = ((61264844909 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0519.s0]
  have e1 : RH1E6S16_0519.sL.t = ((61269216924 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0519.sL]
  rw [e0, e1] at h
  exact h

theorem part_064_3 : RS5.BandZeros ((61260431154 : ℝ) / 65536) ((61269216924 : ℝ) / 65536) 254 := by
  have g0 := band_0518
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0519
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((61260431154 : ℝ) / 65536) ((61269216924 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_064_3 <;> assumption
