-- Prove2me | solution 1 for RH1E6S11.part_084_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T07:01:39.648064+00:00
-- url     : https://prove2.me/submissions/a29c2817-c2d1-45e2-b38a-eb4bf2187bfd

import Definitions.Def_RH1E6S11_D084_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0672 : RS5.BandZeros ((45632723917 : ℝ) / 65536) ((45637208320 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0672.s0 RH1E6S11_0672.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0672.s0 RH1E6S11_0672.rest = RH1E6S11_0672.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0672.s0 :: RH1E6S11_0672.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0672.s0.t = ((45632723917 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0672.s0]
  have e1 : RH1E6S11_0672.sL.t = ((45637208320 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0672.sL]
  rw [e0, e1] at h
  exact h

theorem band_0673 : RS5.BandZeros ((45637208320 : ℝ) / 65536) ((45641719272 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0673.s0 RH1E6S11_0673.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0673.s0 RH1E6S11_0673.rest = RH1E6S11_0673.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0673.s0 :: RH1E6S11_0673.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0673.s0.t = ((45637208320 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0673.s0]
  have e1 : RH1E6S11_0673.sL.t = ((45641719272 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0673.sL]
  rw [e0, e1] at h
  exact h

theorem part_084_0 : RS5.BandZeros ((45632723917 : ℝ) / 65536) ((45641719272 : ℝ) / 65536) 254 := by
  have g0 := band_0672
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0673
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((45632723917 : ℝ) / 65536) ((45641719272 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_084_0 <;> assumption
