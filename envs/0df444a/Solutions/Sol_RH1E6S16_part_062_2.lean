-- Prove2me | solution 1 for RH1E6S16.part_062_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T17:53:39.346427+00:00
-- url     : https://prove2.me/submissions/94a13a1a-72bb-45e5-8ba5-7bc07a090d6a

import Definitions.Def_RH1E6S16_D062_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0500 : RS5.BandZeros ((61181389129 : ℝ) / 65536) ((61185802987 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0500.s0 RH1E6S16_0500.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0500.s0 RH1E6S16_0500.rest = RH1E6S16_0500.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0500.s0 :: RH1E6S16_0500.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0500.s0.t = ((61181389129 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0500.s0]
  have e1 : RH1E6S16_0500.sL.t = ((61185802987 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0500.sL]
  rw [e0, e1] at h
  exact h

theorem band_0501 : RS5.BandZeros ((61185802987 : ℝ) / 65536) ((61190184061 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0501.s0 RH1E6S16_0501.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0501.s0 RH1E6S16_0501.rest = RH1E6S16_0501.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0501.s0 :: RH1E6S16_0501.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0501.s0.t = ((61185802987 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0501.s0]
  have e1 : RH1E6S16_0501.sL.t = ((61190184061 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0501.sL]
  rw [e0, e1] at h
  exact h

theorem part_062_2 : RS5.BandZeros ((61181389129 : ℝ) / 65536) ((61190184061 : ℝ) / 65536) 254 := by
  have g0 := band_0500
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0501
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((61181389129 : ℝ) / 65536) ((61190184061 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_062_2 <;> assumption
