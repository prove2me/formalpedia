-- Prove2me | solution 1 for RH1E6S16.part_018_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T15:05:15.692746+00:00
-- url     : https://prove2.me/submissions/18ca7b59-d5c6-4ed5-ad56-23335a97a9b3

import Definitions.Def_RH1E6S16_D018_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0148 : RS5.BandZeros ((59633999288 : ℝ) / 65536) ((59638412357 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0148.s0 RH1E6S16_0148.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0148.s0 RH1E6S16_0148.rest = RH1E6S16_0148.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0148.s0 :: RH1E6S16_0148.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0148.s0.t = ((59633999288 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0148.s0]
  have e1 : RH1E6S16_0148.sL.t = ((59638412357 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0148.sL]
  rw [e0, e1] at h
  exact h

theorem band_0149 : RS5.BandZeros ((59638412357 : ℝ) / 65536) ((59642799482 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0149.s0 RH1E6S16_0149.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0149.s0 RH1E6S16_0149.rest = RH1E6S16_0149.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0149.s0 :: RH1E6S16_0149.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0149.s0.t = ((59638412357 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0149.s0]
  have e1 : RH1E6S16_0149.sL.t = ((59642799482 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0149.sL]
  rw [e0, e1] at h
  exact h

theorem part_018_2 : RS5.BandZeros ((59633999288 : ℝ) / 65536) ((59642799482 : ℝ) / 65536) 254 := by
  have g0 := band_0148
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0149
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((59633999288 : ℝ) / 65536) ((59642799482 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_018_2 <;> assumption
