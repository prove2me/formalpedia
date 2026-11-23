-- Prove2me | solution 1 for RH1E6S14.part_079_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T07:04:48.153244+00:00
-- url     : https://prove2.me/submissions/c234b8e5-d667-4119-835f-90653c3fc73c

import Definitions.Def_RH1E6S14_D079_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0638 : RS5.BandZeros ((55260857557 : ℝ) / 65536) ((55265283287 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0638.s0 RH1E6S14_0638.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0638.s0 RH1E6S14_0638.rest = RH1E6S14_0638.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0638.s0 :: RH1E6S14_0638.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0638.s0.t = ((55260857557 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0638.s0]
  have e1 : RH1E6S14_0638.sL.t = ((55265283287 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0638.sL]
  rw [e0, e1] at h
  exact h

theorem band_0639 : RS5.BandZeros ((55265283287 : ℝ) / 65536) ((55269710783 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0639.s0 RH1E6S14_0639.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0639.s0 RH1E6S14_0639.rest = RH1E6S14_0639.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0639.s0 :: RH1E6S14_0639.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0639.s0.t = ((55265283287 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0639.s0]
  have e1 : RH1E6S14_0639.sL.t = ((55269710783 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0639.sL]
  rw [e0, e1] at h
  exact h

theorem part_079_3 : RS5.BandZeros ((55260857557 : ℝ) / 65536) ((55269710783 : ℝ) / 65536) 254 := by
  have g0 := band_0638
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0639
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((55260857557 : ℝ) / 65536) ((55269710783 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_079_3 <;> assumption
