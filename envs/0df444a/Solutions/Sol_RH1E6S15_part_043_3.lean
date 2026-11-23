-- Prove2me | solution 1 for RH1E6S15.part_043_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T10:29:27.572514+00:00
-- url     : https://prove2.me/submissions/ac834c64-19a8-4b3c-b682-bb110b14e95a

import Definitions.Def_RH1E6S15_D043_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0350 : RS5.BandZeros ((57252914320 : ℝ) / 65536) ((57257338375 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0350.s0 RH1E6S15_0350.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0350.s0 RH1E6S15_0350.rest = RH1E6S15_0350.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0350.s0 :: RH1E6S15_0350.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0350.s0.t = ((57252914320 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0350.s0]
  have e1 : RH1E6S15_0350.sL.t = ((57257338375 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0350.sL]
  rw [e0, e1] at h
  exact h

theorem band_0351 : RS5.BandZeros ((57257338375 : ℝ) / 65536) ((57261737379 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0351.s0 RH1E6S15_0351.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0351.s0 RH1E6S15_0351.rest = RH1E6S15_0351.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0351.s0 :: RH1E6S15_0351.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0351.s0.t = ((57257338375 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0351.s0]
  have e1 : RH1E6S15_0351.sL.t = ((57261737379 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0351.sL]
  rw [e0, e1] at h
  exact h

theorem part_043_3 : RS5.BandZeros ((57252914320 : ℝ) / 65536) ((57261737379 : ℝ) / 65536) 254 := by
  have g0 := band_0350
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0351
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((57252914320 : ℝ) / 65536) ((57261737379 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_043_3 <;> assumption
