-- Prove2me | solution 1 for RH1E6S07.part_054_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T01:28:37.653242+00:00
-- url     : https://prove2.me/submissions/0454cadd-3e6a-4839-afe9-ba48376c8be9

import Definitions.Def_RH1E6S07_D054_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0432 : RS5.BandZeros ((31506042342 : ℝ) / 65536) ((31510701925 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0432.s0 RH1E6S07_0432.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0432.s0 RH1E6S07_0432.rest = RH1E6S07_0432.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0432.s0 :: RH1E6S07_0432.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0432.s0.t = ((31506042342 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0432.s0]
  have e1 : RH1E6S07_0432.sL.t = ((31510701925 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0432.sL]
  rw [e0, e1] at h
  exact h

theorem band_0433 : RS5.BandZeros ((31510701925 : ℝ) / 65536) ((31515352293 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0433.s0 RH1E6S07_0433.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0433.s0 RH1E6S07_0433.rest = RH1E6S07_0433.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0433.s0 :: RH1E6S07_0433.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0433.s0.t = ((31510701925 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0433.s0]
  have e1 : RH1E6S07_0433.sL.t = ((31515352293 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0433.sL]
  rw [e0, e1] at h
  exact h

theorem part_054_0 : RS5.BandZeros ((31506042342 : ℝ) / 65536) ((31515352293 : ℝ) / 65536) 254 := by
  have g0 := band_0432
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0433
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((31506042342 : ℝ) / 65536) ((31515352293 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_054_0 <;> assumption
