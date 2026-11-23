-- Prove2me | solution 1 for RH1E6S15.part_046_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T10:35:27.66797+00:00
-- url     : https://prove2.me/submissions/9f66d26a-8577-4208-b25b-115cf1140670

import Definitions.Def_RH1E6S15_D046_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0372 : RS5.BandZeros ((57350062531 : ℝ) / 65536) ((57354481063 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0372.s0 RH1E6S15_0372.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0372.s0 RH1E6S15_0372.rest = RH1E6S15_0372.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0372.s0 :: RH1E6S15_0372.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0372.s0.t = ((57350062531 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0372.s0]
  have e1 : RH1E6S15_0372.sL.t = ((57354481063 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0372.sL]
  rw [e0, e1] at h
  exact h

theorem band_0373 : RS5.BandZeros ((57354481063 : ℝ) / 65536) ((57358905134 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0373.s0 RH1E6S15_0373.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0373.s0 RH1E6S15_0373.rest = RH1E6S15_0373.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0373.s0 :: RH1E6S15_0373.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0373.s0.t = ((57354481063 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0373.s0]
  have e1 : RH1E6S15_0373.sL.t = ((57358905134 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0373.sL]
  rw [e0, e1] at h
  exact h

theorem part_046_2 : RS5.BandZeros ((57350062531 : ℝ) / 65536) ((57358905134 : ℝ) / 65536) 254 := by
  have g0 := band_0372
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0373
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((57350062531 : ℝ) / 65536) ((57358905134 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_046_2 <;> assumption
