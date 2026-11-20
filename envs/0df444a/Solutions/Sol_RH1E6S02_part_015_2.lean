-- Prove2me | solution 1 for RH1E6S02.part_015_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T02:39:28.92298+00:00
-- url     : https://prove2.me/submissions/84f0967a-ba2a-41c3-8b78-1dc70ea213b4

import Definitions.Def_RH1E6S02_D015_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0124 : RS5.BandZeros ((13731230669 : ℝ) / 65536) ((13736258413 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0124.s0 RH1E6S02_0124.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0124.s0 RH1E6S02_0124.rest = RH1E6S02_0124.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0124.s0 :: RH1E6S02_0124.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0124.s0.t = ((13731230669 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0124.s0]
  have e1 : RH1E6S02_0124.sL.t = ((13736258413 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0124.sL]
  rw [e0, e1] at h
  exact h

theorem band_0125 : RS5.BandZeros ((13736258413 : ℝ) / 65536) ((13741264474 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0125.s0 RH1E6S02_0125.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0125.s0 RH1E6S02_0125.rest = RH1E6S02_0125.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0125.s0 :: RH1E6S02_0125.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0125.s0.t = ((13736258413 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0125.s0]
  have e1 : RH1E6S02_0125.sL.t = ((13741264474 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0125.sL]
  rw [e0, e1] at h
  exact h

theorem part_015_2 : RS5.BandZeros ((13731230669 : ℝ) / 65536) ((13741264474 : ℝ) / 65536) 254 := by
  have g0 := band_0124
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0125
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((13731230669 : ℝ) / 65536) ((13741264474 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_015_2 <;> assumption
