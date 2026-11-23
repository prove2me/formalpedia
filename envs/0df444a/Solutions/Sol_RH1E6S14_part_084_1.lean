-- Prove2me | solution 1 for RH1E6S14.part_084_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T07:16:56.672924+00:00
-- url     : https://prove2.me/submissions/8043aeb8-0224-4231-a390-10b60789659c

import Definitions.Def_RH1E6S14_D084_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0674 : RS5.BandZeros ((55420267176 : ℝ) / 65536) ((55424704356 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0674.s0 RH1E6S14_0674.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0674.s0 RH1E6S14_0674.rest = RH1E6S14_0674.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0674.s0 :: RH1E6S14_0674.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0674.s0.t = ((55420267176 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0674.s0]
  have e1 : RH1E6S14_0674.sL.t = ((55424704356 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0674.sL]
  rw [e0, e1] at h
  exact h

theorem band_0675 : RS5.BandZeros ((55424704356 : ℝ) / 65536) ((55429118153 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0675.s0 RH1E6S14_0675.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0675.s0 RH1E6S14_0675.rest = RH1E6S14_0675.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0675.s0 :: RH1E6S14_0675.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0675.s0.t = ((55424704356 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0675.s0]
  have e1 : RH1E6S14_0675.sL.t = ((55429118153 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0675.sL]
  rw [e0, e1] at h
  exact h

theorem part_084_1 : RS5.BandZeros ((55420267176 : ℝ) / 65536) ((55429118153 : ℝ) / 65536) 254 := by
  have g0 := band_0674
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0675
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((55420267176 : ℝ) / 65536) ((55429118153 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_084_1 <;> assumption
