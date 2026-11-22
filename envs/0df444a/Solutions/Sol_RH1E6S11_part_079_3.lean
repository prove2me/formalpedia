-- Prove2me | solution 1 for RH1E6S11.part_079_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T06:50:06.30699+00:00
-- url     : https://prove2.me/submissions/d63b97c3-ea1c-4f41-86bf-bd8ee347aaab

import Definitions.Def_RH1E6S11_D079_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0638 : RS5.BandZeros ((45479628787 : ℝ) / 65536) ((45484141082 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0638.s0 RH1E6S11_0638.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0638.s0 RH1E6S11_0638.rest = RH1E6S11_0638.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0638.s0 :: RH1E6S11_0638.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0638.s0.t = ((45479628787 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0638.s0]
  have e1 : RH1E6S11_0638.sL.t = ((45484141082 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0638.sL]
  rw [e0, e1] at h
  exact h

theorem band_0639 : RS5.BandZeros ((45484141082 : ℝ) / 65536) ((45488635610 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0639.s0 RH1E6S11_0639.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0639.s0 RH1E6S11_0639.rest = RH1E6S11_0639.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0639.s0 :: RH1E6S11_0639.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0639.s0.t = ((45484141082 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0639.s0]
  have e1 : RH1E6S11_0639.sL.t = ((45488635610 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0639.sL]
  rw [e0, e1] at h
  exact h

theorem part_079_3 : RS5.BandZeros ((45479628787 : ℝ) / 65536) ((45488635610 : ℝ) / 65536) 254 := by
  have g0 := band_0638
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0639
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((45479628787 : ℝ) / 65536) ((45488635610 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_079_3 <;> assumption
