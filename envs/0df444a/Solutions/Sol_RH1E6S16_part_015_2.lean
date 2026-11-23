-- Prove2me | solution 1 for RH1E6S16.part_015_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T14:50:24.107976+00:00
-- url     : https://prove2.me/submissions/6f4201e6-756f-4c08-84b3-72335f578063

import Definitions.Def_RH1E6S16_D015_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0124 : RS5.BandZeros ((59528386427 : ℝ) / 65536) ((59532793684 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0124.s0 RH1E6S16_0124.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0124.s0 RH1E6S16_0124.rest = RH1E6S16_0124.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0124.s0 :: RH1E6S16_0124.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0124.s0.t = ((59528386427 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0124.s0]
  have e1 : RH1E6S16_0124.sL.t = ((59532793684 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0124.sL]
  rw [e0, e1] at h
  exact h

theorem band_0125 : RS5.BandZeros ((59532793684 : ℝ) / 65536) ((59537163681 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0125.s0 RH1E6S16_0125.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0125.s0 RH1E6S16_0125.rest = RH1E6S16_0125.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0125.s0 :: RH1E6S16_0125.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0125.s0.t = ((59532793684 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0125.s0]
  have e1 : RH1E6S16_0125.sL.t = ((59537163681 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0125.sL]
  rw [e0, e1] at h
  exact h

theorem part_015_2 : RS5.BandZeros ((59528386427 : ℝ) / 65536) ((59537163681 : ℝ) / 65536) 254 := by
  have g0 := band_0124
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0125
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((59528386427 : ℝ) / 65536) ((59537163681 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_015_2 <;> assumption
