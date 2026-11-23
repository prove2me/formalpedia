-- Prove2me | solution 1 for RH1E6S16.part_054_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T17:16:44.132805+00:00
-- url     : https://prove2.me/submissions/13ddb852-6653-438b-9144-3895431925ba

import Definitions.Def_RH1E6S16_D054_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0432 : RS5.BandZeros ((60882726288 : ℝ) / 65536) ((60887127476 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0432.s0 RH1E6S16_0432.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0432.s0 RH1E6S16_0432.rest = RH1E6S16_0432.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0432.s0 :: RH1E6S16_0432.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0432.s0.t = ((60882726288 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0432.s0]
  have e1 : RH1E6S16_0432.sL.t = ((60887127476 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0432.sL]
  rw [e0, e1] at h
  exact h

theorem band_0433 : RS5.BandZeros ((60887127476 : ℝ) / 65536) ((60891509786 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0433.s0 RH1E6S16_0433.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0433.s0 RH1E6S16_0433.rest = RH1E6S16_0433.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0433.s0 :: RH1E6S16_0433.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0433.s0.t = ((60887127476 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0433.s0]
  have e1 : RH1E6S16_0433.sL.t = ((60891509786 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0433.sL]
  rw [e0, e1] at h
  exact h

theorem part_054_0 : RS5.BandZeros ((60882726288 : ℝ) / 65536) ((60891509786 : ℝ) / 65536) 254 := by
  have g0 := band_0432
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0433
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((60882726288 : ℝ) / 65536) ((60891509786 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_054_0 <;> assumption
