-- Prove2me | solution 1 for RH1E6S16.part_019_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T15:08:25.863288+00:00
-- url     : https://prove2.me/submissions/51a52e8f-f99b-42a8-bce6-351bc8d95b72

import Definitions.Def_RH1E6S16_D019_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0158 : RS5.BandZeros ((59678001997 : ℝ) / 65536) ((59682428460 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0158.s0 RH1E6S16_0158.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0158.s0 RH1E6S16_0158.rest = RH1E6S16_0158.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0158.s0 :: RH1E6S16_0158.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0158.s0.t = ((59678001997 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0158.s0]
  have e1 : RH1E6S16_0158.sL.t = ((59682428460 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0158.sL]
  rw [e0, e1] at h
  exact h

theorem band_0159 : RS5.BandZeros ((59682428460 : ℝ) / 65536) ((59686802921 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0159.s0 RH1E6S16_0159.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0159.s0 RH1E6S16_0159.rest = RH1E6S16_0159.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0159.s0 :: RH1E6S16_0159.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0159.s0.t = ((59682428460 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0159.s0]
  have e1 : RH1E6S16_0159.sL.t = ((59686802921 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0159.sL]
  rw [e0, e1] at h
  exact h

theorem part_019_3 : RS5.BandZeros ((59678001997 : ℝ) / 65536) ((59686802921 : ℝ) / 65536) 254 := by
  have g0 := band_0158
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0159
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((59678001997 : ℝ) / 65536) ((59686802921 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_019_3 <;> assumption
