-- Prove2me | solution 1 for RH1E6S16.part_091_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T19:25:06.445234+00:00
-- url     : https://prove2.me/submissions/f51d7c4c-b802-4f92-8211-8b05b4923a55

import Definitions.Def_RH1E6S16_D091_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0730 : RS5.BandZeros ((62190703473 : ℝ) / 65536) ((62195081997 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0730.s0 RH1E6S16_0730.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0730.s0 RH1E6S16_0730.rest = RH1E6S16_0730.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0730.s0 :: RH1E6S16_0730.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0730.s0.t = ((62190703473 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0730.s0]
  have e1 : RH1E6S16_0730.sL.t = ((62195081997 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0730.sL]
  rw [e0, e1] at h
  exact h

theorem band_0731 : RS5.BandZeros ((62195081997 : ℝ) / 65536) ((62199471072 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0731.s0 RH1E6S16_0731.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0731.s0 RH1E6S16_0731.rest = RH1E6S16_0731.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0731.s0 :: RH1E6S16_0731.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0731.s0.t = ((62195081997 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0731.s0]
  have e1 : RH1E6S16_0731.sL.t = ((62199471072 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0731.sL]
  rw [e0, e1] at h
  exact h

theorem part_091_1 : RS5.BandZeros ((62190703473 : ℝ) / 65536) ((62199471072 : ℝ) / 65536) 254 := by
  have g0 := band_0730
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0731
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((62190703473 : ℝ) / 65536) ((62199471072 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_091_1 <;> assumption
