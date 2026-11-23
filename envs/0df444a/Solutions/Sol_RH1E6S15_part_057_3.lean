-- Prove2me | solution 1 for RH1E6S15.part_057_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T11:22:21.198494+00:00
-- url     : https://prove2.me/submissions/74dc588d-5800-4ede-a0a7-406dae428a0c

import Definitions.Def_RH1E6S15_D057_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0462 : RS5.BandZeros ((57747309360 : ℝ) / 65536) ((57751737256 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0462.s0 RH1E6S15_0462.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0462.s0 RH1E6S15_0462.rest = RH1E6S15_0462.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0462.s0 :: RH1E6S15_0462.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0462.s0.t = ((57747309360 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0462.s0]
  have e1 : RH1E6S15_0462.sL.t = ((57751737256 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0462.sL]
  rw [e0, e1] at h
  exact h

theorem band_0463 : RS5.BandZeros ((57751737256 : ℝ) / 65536) ((57756139351 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0463.s0 RH1E6S15_0463.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0463.s0 RH1E6S15_0463.rest = RH1E6S15_0463.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0463.s0 :: RH1E6S15_0463.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0463.s0.t = ((57751737256 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0463.s0]
  have e1 : RH1E6S15_0463.sL.t = ((57756139351 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0463.sL]
  rw [e0, e1] at h
  exact h

theorem part_057_3 : RS5.BandZeros ((57747309360 : ℝ) / 65536) ((57756139351 : ℝ) / 65536) 254 := by
  have g0 := band_0462
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0463
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((57747309360 : ℝ) / 65536) ((57756139351 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_057_3 <;> assumption
