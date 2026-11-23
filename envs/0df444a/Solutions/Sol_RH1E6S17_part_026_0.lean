-- Prove2me | solution 1 for RH1E6S17.part_026_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T20:59:34.840798+00:00
-- url     : https://prove2.me/submissions/ad28f615-569e-4f51-8ed8-81e983b5e4da

import Definitions.Def_RH1E6S17_D026_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0208 : RS5.BandZeros ((63170699703 : ℝ) / 65536) ((63175079219 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0208.s0 RH1E6S17_0208.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0208.s0 RH1E6S17_0208.rest = RH1E6S17_0208.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0208.s0 :: RH1E6S17_0208.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0208.s0.t = ((63170699703 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0208.s0]
  have e1 : RH1E6S17_0208.sL.t = ((63175079219 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0208.sL]
  rw [e0, e1] at h
  exact h

theorem band_0209 : RS5.BandZeros ((63175079219 : ℝ) / 65536) ((63179467330 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0209.s0 RH1E6S17_0209.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0209.s0 RH1E6S17_0209.rest = RH1E6S17_0209.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0209.s0 :: RH1E6S17_0209.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0209.s0.t = ((63175079219 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0209.s0]
  have e1 : RH1E6S17_0209.sL.t = ((63179467330 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0209.sL]
  rw [e0, e1] at h
  exact h

theorem part_026_0 : RS5.BandZeros ((63170699703 : ℝ) / 65536) ((63179467330 : ℝ) / 65536) 254 := by
  have g0 := band_0208
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0209
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((63170699703 : ℝ) / 65536) ((63179467330 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_026_0 <;> assumption
