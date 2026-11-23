-- Prove2me | solution 1 for RH1E6S13.part_064_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T00:36:45.059632+00:00
-- url     : https://prove2.me/submissions/2be41130-bab5-402d-a626-fc4421655f8d

import Definitions.Def_RH1E6S13_D064_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0514 : RS5.BandZeros ((51446889571 : ℝ) / 65536) ((51451328151 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0514.s0 RH1E6S13_0514.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0514.s0 RH1E6S13_0514.rest = RH1E6S13_0514.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0514.s0 :: RH1E6S13_0514.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0514.s0.t = ((51446889571 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0514.s0]
  have e1 : RH1E6S13_0514.sL.t = ((51451328151 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0514.sL]
  rw [e0, e1] at h
  exact h

theorem band_0515 : RS5.BandZeros ((51451328151 : ℝ) / 65536) ((51455801785 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0515.s0 RH1E6S13_0515.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0515.s0 RH1E6S13_0515.rest = RH1E6S13_0515.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0515.s0 :: RH1E6S13_0515.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0515.s0.t = ((51451328151 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0515.s0]
  have e1 : RH1E6S13_0515.sL.t = ((51455801785 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0515.sL]
  rw [e0, e1] at h
  exact h

theorem part_064_1 : RS5.BandZeros ((51446889571 : ℝ) / 65536) ((51455801785 : ℝ) / 65536) 254 := by
  have g0 := band_0514
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0515
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((51446889571 : ℝ) / 65536) ((51455801785 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_064_1 <;> assumption
