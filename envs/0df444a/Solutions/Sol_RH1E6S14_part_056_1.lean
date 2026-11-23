-- Prove2me | solution 1 for RH1E6S14.part_056_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T05:44:03.891805+00:00
-- url     : https://prove2.me/submissions/da8bf973-8eea-4f0f-991c-6aeef9962b2c

import Definitions.Def_RH1E6S14_D056_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0450 : RS5.BandZeros ((54427625648 : ℝ) / 65536) ((54432074919 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0450.s0 RH1E6S14_0450.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0450.s0 RH1E6S14_0450.rest = RH1E6S14_0450.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0450.s0 :: RH1E6S14_0450.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0450.s0.t = ((54427625648 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0450.s0]
  have e1 : RH1E6S14_0450.sL.t = ((54432074919 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0450.sL]
  rw [e0, e1] at h
  exact h

theorem band_0451 : RS5.BandZeros ((54432074919 : ℝ) / 65536) ((54436504028 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0451.s0 RH1E6S14_0451.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0451.s0 RH1E6S14_0451.rest = RH1E6S14_0451.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0451.s0 :: RH1E6S14_0451.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0451.s0.t = ((54432074919 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0451.s0]
  have e1 : RH1E6S14_0451.sL.t = ((54436504028 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0451.sL]
  rw [e0, e1] at h
  exact h

theorem part_056_1 : RS5.BandZeros ((54427625648 : ℝ) / 65536) ((54436504028 : ℝ) / 65536) 254 := by
  have g0 := band_0450
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0451
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((54427625648 : ℝ) / 65536) ((54436504028 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_056_1 <;> assumption
