-- Prove2me | solution 1 for RH1E6S16.part_050_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T17:01:32.350039+00:00
-- url     : https://prove2.me/submissions/10ef9dcb-43d8-4476-a65c-f73db03c1ef4

import Definitions.Def_RH1E6S16_D050_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0402 : RS5.BandZeros ((60750929217 : ℝ) / 65536) ((60755315148 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0402.s0 RH1E6S16_0402.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0402.s0 RH1E6S16_0402.rest = RH1E6S16_0402.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0402.s0 :: RH1E6S16_0402.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0402.s0.t = ((60750929217 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0402.s0]
  have e1 : RH1E6S16_0402.sL.t = ((60755315148 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0402.sL]
  rw [e0, e1] at h
  exact h

theorem band_0403 : RS5.BandZeros ((60755315148 : ℝ) / 65536) ((60759697299 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0403.s0 RH1E6S16_0403.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0403.s0 RH1E6S16_0403.rest = RH1E6S16_0403.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0403.s0 :: RH1E6S16_0403.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0403.s0.t = ((60755315148 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0403.s0]
  have e1 : RH1E6S16_0403.sL.t = ((60759697299 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0403.sL]
  rw [e0, e1] at h
  exact h

theorem part_050_1 : RS5.BandZeros ((60750929217 : ℝ) / 65536) ((60759697299 : ℝ) / 65536) 254 := by
  have g0 := band_0402
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0403
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((60750929217 : ℝ) / 65536) ((60759697299 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_050_1 <;> assumption
