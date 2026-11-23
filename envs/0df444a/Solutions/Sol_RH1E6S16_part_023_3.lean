-- Prove2me | solution 1 for RH1E6S16.part_023_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T15:23:39.129075+00:00
-- url     : https://prove2.me/submissions/813c7bad-8a60-4444-b137-50ea084f1da4

import Definitions.Def_RH1E6S16_D023_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0190 : RS5.BandZeros ((59818812789 : ℝ) / 65536) ((59823220614 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0190.s0 RH1E6S16_0190.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0190.s0 RH1E6S16_0190.rest = RH1E6S16_0190.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0190.s0 :: RH1E6S16_0190.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0190.s0.t = ((59818812789 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0190.s0]
  have e1 : RH1E6S16_0190.sL.t = ((59823220614 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0190.sL]
  rw [e0, e1] at h
  exact h

theorem band_0191 : RS5.BandZeros ((59823220614 : ℝ) / 65536) ((59827607585 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0191.s0 RH1E6S16_0191.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0191.s0 RH1E6S16_0191.rest = RH1E6S16_0191.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0191.s0 :: RH1E6S16_0191.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0191.s0.t = ((59823220614 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0191.s0]
  have e1 : RH1E6S16_0191.sL.t = ((59827607585 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0191.sL]
  rw [e0, e1] at h
  exact h

theorem part_023_3 : RS5.BandZeros ((59818812789 : ℝ) / 65536) ((59827607585 : ℝ) / 65536) 254 := by
  have g0 := band_0190
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0191
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((59818812789 : ℝ) / 65536) ((59827607585 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_023_3 <;> assumption
