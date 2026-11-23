-- Prove2me | solution 1 for RH1E6S15.part_072_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T12:21:16.456904+00:00
-- url     : https://prove2.me/submissions/bce6cce2-79cc-4e2c-8bb8-ac6a64b97598

import Definitions.Def_RH1E6S15_D072_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0578 : RS5.BandZeros ((58259001554 : ℝ) / 65536) ((58263404740 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0578.s0 RH1E6S15_0578.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0578.s0 RH1E6S15_0578.rest = RH1E6S15_0578.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0578.s0 :: RH1E6S15_0578.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0578.s0.t = ((58259001554 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0578.s0]
  have e1 : RH1E6S15_0578.sL.t = ((58263404740 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0578.sL]
  rw [e0, e1] at h
  exact h

theorem band_0579 : RS5.BandZeros ((58263404740 : ℝ) / 65536) ((58267840540 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0579.s0 RH1E6S15_0579.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0579.s0 RH1E6S15_0579.rest = RH1E6S15_0579.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0579.s0 :: RH1E6S15_0579.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0579.s0.t = ((58263404740 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0579.s0]
  have e1 : RH1E6S15_0579.sL.t = ((58267840540 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0579.sL]
  rw [e0, e1] at h
  exact h

theorem part_072_1 : RS5.BandZeros ((58259001554 : ℝ) / 65536) ((58267840540 : ℝ) / 65536) 254 := by
  have g0 := band_0578
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0579
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((58259001554 : ℝ) / 65536) ((58267840540 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_072_1 <;> assumption
