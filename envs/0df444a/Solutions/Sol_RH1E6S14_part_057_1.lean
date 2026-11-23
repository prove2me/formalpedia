-- Prove2me | solution 1 for RH1E6S14.part_057_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T05:47:03.664374+00:00
-- url     : https://prove2.me/submissions/4cb8bac6-a901-4c23-b33d-756a9a9c03d1

import Definitions.Def_RH1E6S14_D057_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0458 : RS5.BandZeros ((54463120974 : ℝ) / 65536) ((54467552780 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0458.s0 RH1E6S14_0458.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0458.s0 RH1E6S14_0458.rest = RH1E6S14_0458.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0458.s0 :: RH1E6S14_0458.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0458.s0.t = ((54463120974 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0458.s0]
  have e1 : RH1E6S14_0458.sL.t = ((54467552780 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0458.sL]
  rw [e0, e1] at h
  exact h

theorem band_0459 : RS5.BandZeros ((54467552780 : ℝ) / 65536) ((54471975106 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0459.s0 RH1E6S14_0459.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0459.s0 RH1E6S14_0459.rest = RH1E6S14_0459.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0459.s0 :: RH1E6S14_0459.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0459.s0.t = ((54467552780 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0459.s0]
  have e1 : RH1E6S14_0459.sL.t = ((54471975106 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0459.sL]
  rw [e0, e1] at h
  exact h

theorem part_057_1 : RS5.BandZeros ((54463120974 : ℝ) / 65536) ((54471975106 : ℝ) / 65536) 254 := by
  have g0 := band_0458
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0459
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((54463120974 : ℝ) / 65536) ((54471975106 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_057_1 <;> assumption
