-- Prove2me | solution 1 for RH1E6S11.part_079_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T06:47:18.906725+00:00
-- url     : https://prove2.me/submissions/1b294224-6cef-4561-9b3d-77cf4a967147

import Definitions.Def_RH1E6S11_D079_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0636 : RS5.BandZeros ((45470621810 : ℝ) / 65536) ((45475143048 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0636.s0 RH1E6S11_0636.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0636.s0 RH1E6S11_0636.rest = RH1E6S11_0636.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0636.s0 :: RH1E6S11_0636.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0636.s0.t = ((45470621810 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0636.s0]
  have e1 : RH1E6S11_0636.sL.t = ((45475143048 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0636.sL]
  rw [e0, e1] at h
  exact h

theorem band_0637 : RS5.BandZeros ((45475143048 : ℝ) / 65536) ((45479628787 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0637.s0 RH1E6S11_0637.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0637.s0 RH1E6S11_0637.rest = RH1E6S11_0637.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0637.s0 :: RH1E6S11_0637.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0637.s0.t = ((45475143048 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0637.s0]
  have e1 : RH1E6S11_0637.sL.t = ((45479628787 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0637.sL]
  rw [e0, e1] at h
  exact h

theorem part_079_2 : RS5.BandZeros ((45470621810 : ℝ) / 65536) ((45479628787 : ℝ) / 65536) 254 := by
  have g0 := band_0636
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0637
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((45470621810 : ℝ) / 65536) ((45479628787 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_079_2 <;> assumption
