-- Prove2me | solution 1 for RH1E6S15.part_035_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T09:53:59.113924+00:00
-- url     : https://prove2.me/submissions/ba0b47ff-acf2-40c2-a299-2081872e14d1

import Definitions.Def_RH1E6S15_D035_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0280 : RS5.BandZeros ((56943733340 : ℝ) / 65536) ((56948148293 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0280.s0 RH1E6S15_0280.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0280.s0 RH1E6S15_0280.rest = RH1E6S15_0280.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0280.s0 :: RH1E6S15_0280.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0280.s0.t = ((56943733340 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0280.s0]
  have e1 : RH1E6S15_0280.sL.t = ((56948148293 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0280.sL]
  rw [e0, e1] at h
  exact h

theorem band_0281 : RS5.BandZeros ((56948148293 : ℝ) / 65536) ((56952574871 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0281.s0 RH1E6S15_0281.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0281.s0 RH1E6S15_0281.rest = RH1E6S15_0281.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0281.s0 :: RH1E6S15_0281.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0281.s0.t = ((56948148293 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0281.s0]
  have e1 : RH1E6S15_0281.sL.t = ((56952574871 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0281.sL]
  rw [e0, e1] at h
  exact h

theorem part_035_0 : RS5.BandZeros ((56943733340 : ℝ) / 65536) ((56952574871 : ℝ) / 65536) 254 := by
  have g0 := band_0280
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0281
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((56943733340 : ℝ) / 65536) ((56952574871 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_035_0 <;> assumption
