-- Prove2me | solution 1 for RH1E6S16.part_066_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T18:06:04.674743+00:00
-- url     : https://prove2.me/submissions/09a4c4d7-6f88-478a-b49d-1c951d59d1a3

import Definitions.Def_RH1E6S16_D066_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0530 : RS5.BandZeros ((61313124753 : ℝ) / 65536) ((61317506729 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0530.s0 RH1E6S16_0530.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0530.s0 RH1E6S16_0530.rest = RH1E6S16_0530.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0530.s0 :: RH1E6S16_0530.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0530.s0.t = ((61313124753 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0530.s0]
  have e1 : RH1E6S16_0530.sL.t = ((61317506729 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0530.sL]
  rw [e0, e1] at h
  exact h

theorem band_0531 : RS5.BandZeros ((61317506729 : ℝ) / 65536) ((61321906913 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0531.s0 RH1E6S16_0531.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0531.s0 RH1E6S16_0531.rest = RH1E6S16_0531.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0531.s0 :: RH1E6S16_0531.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0531.s0.t = ((61317506729 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0531.s0]
  have e1 : RH1E6S16_0531.sL.t = ((61321906913 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0531.sL]
  rw [e0, e1] at h
  exact h

theorem part_066_1 : RS5.BandZeros ((61313124753 : ℝ) / 65536) ((61321906913 : ℝ) / 65536) 254 := by
  have g0 := band_0530
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0531
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((61313124753 : ℝ) / 65536) ((61321906913 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_066_1 <;> assumption
