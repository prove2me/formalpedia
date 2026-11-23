-- Prove2me | solution 1 for RH1E6S15.part_014_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T08:39:50.948523+00:00
-- url     : https://prove2.me/submissions/09c78fd8-74dd-4c08-a990-03c659738620

import Definitions.Def_RH1E6S15_D014_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0112 : RS5.BandZeros ((56201123644 : ℝ) / 65536) ((56205513583 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0112.s0 RH1E6S15_0112.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0112.s0 RH1E6S15_0112.rest = RH1E6S15_0112.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0112.s0 :: RH1E6S15_0112.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0112.s0.t = ((56201123644 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0112.s0]
  have e1 : RH1E6S15_0112.sL.t = ((56205513583 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0112.sL]
  rw [e0, e1] at h
  exact h

theorem band_0113 : RS5.BandZeros ((56205513583 : ℝ) / 65536) ((56209956901 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0113.s0 RH1E6S15_0113.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0113.s0 RH1E6S15_0113.rest = RH1E6S15_0113.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0113.s0 :: RH1E6S15_0113.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0113.s0.t = ((56205513583 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0113.s0]
  have e1 : RH1E6S15_0113.sL.t = ((56209956901 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0113.sL]
  rw [e0, e1] at h
  exact h

theorem part_014_0 : RS5.BandZeros ((56201123644 : ℝ) / 65536) ((56209956901 : ℝ) / 65536) 254 := by
  have g0 := band_0112
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0113
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((56201123644 : ℝ) / 65536) ((56209956901 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_014_0 <;> assumption
