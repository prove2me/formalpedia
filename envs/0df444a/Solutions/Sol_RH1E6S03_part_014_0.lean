-- Prove2me | solution 1 for RH1E6S03.part_014_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T05:46:04.6472+00:00
-- url     : https://prove2.me/submissions/1ba93d8c-d267-485a-9dc3-e9dcc60b812b

import Definitions.Def_RH1E6S03_D014_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0112 : RS5.BandZeros ((16936123491 : ℝ) / 65536) ((16941055273 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0112.s0 RH1E6S03_0112.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0112.s0 RH1E6S03_0112.rest = RH1E6S03_0112.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0112.s0 :: RH1E6S03_0112.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0112.s0.t = ((16936123491 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0112.s0]
  have e1 : RH1E6S03_0112.sL.t = ((16941055273 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0112.sL]
  rw [e0, e1] at h
  exact h

theorem band_0113 : RS5.BandZeros ((16941055273 : ℝ) / 65536) ((16945967542 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0113.s0 RH1E6S03_0113.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0113.s0 RH1E6S03_0113.rest = RH1E6S03_0113.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0113.s0 :: RH1E6S03_0113.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0113.s0.t = ((16941055273 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0113.s0]
  have e1 : RH1E6S03_0113.sL.t = ((16945967542 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0113.sL]
  rw [e0, e1] at h
  exact h

theorem part_014_0 : RS5.BandZeros ((16936123491 : ℝ) / 65536) ((16945967542 : ℝ) / 65536) 254 := by
  have g0 := band_0112
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0113
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((16936123491 : ℝ) / 65536) ((16945967542 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_014_0 <;> assumption
