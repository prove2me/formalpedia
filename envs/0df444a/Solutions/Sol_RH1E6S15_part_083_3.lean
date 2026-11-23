-- Prove2me | solution 1 for RH1E6S15.part_083_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T13:14:58.375408+00:00
-- url     : https://prove2.me/submissions/e05e0c00-a5e7-486c-a6da-e1c7f32d0149

import Definitions.Def_RH1E6S15_D083_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0670 : RS5.BandZeros ((58664537641 : ℝ) / 65536) ((58668961373 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0670.s0 RH1E6S15_0670.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0670.s0 RH1E6S15_0670.rest = RH1E6S15_0670.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0670.s0 :: RH1E6S15_0670.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0670.s0.t = ((58664537641 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0670.s0]
  have e1 : RH1E6S15_0670.sL.t = ((58668961373 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0670.sL]
  rw [e0, e1] at h
  exact h

theorem band_0671 : RS5.BandZeros ((58668961373 : ℝ) / 65536) ((58673356989 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0671.s0 RH1E6S15_0671.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0671.s0 RH1E6S15_0671.rest = RH1E6S15_0671.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0671.s0 :: RH1E6S15_0671.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0671.s0.t = ((58668961373 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0671.s0]
  have e1 : RH1E6S15_0671.sL.t = ((58673356989 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0671.sL]
  rw [e0, e1] at h
  exact h

theorem part_083_3 : RS5.BandZeros ((58664537641 : ℝ) / 65536) ((58673356989 : ℝ) / 65536) 254 := by
  have g0 := band_0670
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0671
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((58664537641 : ℝ) / 65536) ((58673356989 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_083_3 <;> assumption
