-- Prove2me | solution 1 for RH1E6S11.part_014_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T03:40:28.315228+00:00
-- url     : https://prove2.me/submissions/64a5a666-8fe6-41be-aac8-82a1bda06d9a

import Definitions.Def_RH1E6S11_D014_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0112 : RS5.BandZeros ((43105373004 : ℝ) / 65536) ((43109897324 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0112.s0 RH1E6S11_0112.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0112.s0 RH1E6S11_0112.rest = RH1E6S11_0112.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0112.s0 :: RH1E6S11_0112.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0112.s0.t = ((43105373004 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0112.s0]
  have e1 : RH1E6S11_0112.sL.t = ((43109897324 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0112.sL]
  rw [e0, e1] at h
  exact h

theorem band_0113 : RS5.BandZeros ((43109897324 : ℝ) / 65536) ((43114448320 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0113.s0 RH1E6S11_0113.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0113.s0 RH1E6S11_0113.rest = RH1E6S11_0113.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0113.s0 :: RH1E6S11_0113.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0113.s0.t = ((43109897324 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0113.s0]
  have e1 : RH1E6S11_0113.sL.t = ((43114448320 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0113.sL]
  rw [e0, e1] at h
  exact h

theorem part_014_0 : RS5.BandZeros ((43105373004 : ℝ) / 65536) ((43114448320 : ℝ) / 65536) 254 := by
  have g0 := band_0112
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0113
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((43105373004 : ℝ) / 65536) ((43114448320 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_014_0 <;> assumption
