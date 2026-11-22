-- Prove2me | solution 1 for RH1E6S11.part_062_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T06:01:43.560417+00:00
-- url     : https://prove2.me/submissions/ab24b12d-e5b6-42b0-9d11-cd4350662c84

import Definitions.Def_RH1E6S11_D062_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0498 : RS5.BandZeros ((44848767257 : ℝ) / 65536) ((44853284987 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0498.s0 RH1E6S11_0498.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0498.s0 RH1E6S11_0498.rest = RH1E6S11_0498.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0498.s0 :: RH1E6S11_0498.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0498.s0.t = ((44848767257 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0498.s0]
  have e1 : RH1E6S11_0498.sL.t = ((44853284987 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0498.sL]
  rw [e0, e1] at h
  exact h

theorem band_0499 : RS5.BandZeros ((44853284987 : ℝ) / 65536) ((44857784926 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0499.s0 RH1E6S11_0499.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0499.s0 RH1E6S11_0499.rest = RH1E6S11_0499.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0499.s0 :: RH1E6S11_0499.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0499.s0.t = ((44853284987 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0499.s0]
  have e1 : RH1E6S11_0499.sL.t = ((44857784926 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0499.sL]
  rw [e0, e1] at h
  exact h

theorem part_062_1 : RS5.BandZeros ((44848767257 : ℝ) / 65536) ((44857784926 : ℝ) / 65536) 254 := by
  have g0 := band_0498
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0499
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((44848767257 : ℝ) / 65536) ((44857784926 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_062_1 <;> assumption
