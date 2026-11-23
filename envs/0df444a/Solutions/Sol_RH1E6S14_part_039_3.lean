-- Prove2me | solution 1 for RH1E6S14.part_039_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T04:49:52.712433+00:00
-- url     : https://prove2.me/submissions/3a724e3d-54e6-4a58-b6f1-546aa128d017

import Definitions.Def_RH1E6S14_D039_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0318 : RS5.BandZeros ((53841973949 : ℝ) / 65536) ((53846389304 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0318.s0 RH1E6S14_0318.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0318.s0 RH1E6S14_0318.rest = RH1E6S14_0318.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0318.s0 :: RH1E6S14_0318.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0318.s0.t = ((53841973949 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0318.s0]
  have e1 : RH1E6S14_0318.sL.t = ((53846389304 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0318.sL]
  rw [e0, e1] at h
  exact h

theorem band_0319 : RS5.BandZeros ((53846389304 : ℝ) / 65536) ((53850843006 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0319.s0 RH1E6S14_0319.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0319.s0 RH1E6S14_0319.rest = RH1E6S14_0319.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0319.s0 :: RH1E6S14_0319.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0319.s0.t = ((53846389304 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0319.s0]
  have e1 : RH1E6S14_0319.sL.t = ((53850843006 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0319.sL]
  rw [e0, e1] at h
  exact h

theorem part_039_3 : RS5.BandZeros ((53841973949 : ℝ) / 65536) ((53850843006 : ℝ) / 65536) 254 := by
  have g0 := band_0318
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0319
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((53841973949 : ℝ) / 65536) ((53850843006 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_039_3 <;> assumption
