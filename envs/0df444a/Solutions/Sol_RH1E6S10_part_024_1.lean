-- Prove2me | solution 1 for RH1E6S10.part_024_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T22:21:15.318749+00:00
-- url     : https://prove2.me/submissions/7905ad48-4aec-40d8-b81e-f27362b9b06e

import Definitions.Def_RH1E6S10_D024_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0194 : RS5.BandZeros ((40205506924 : ℝ) / 65536) ((40210085547 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0194.s0 RH1E6S10_0194.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0194.s0 RH1E6S10_0194.rest = RH1E6S10_0194.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0194.s0 :: RH1E6S10_0194.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0194.s0.t = ((40205506924 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0194.s0]
  have e1 : RH1E6S10_0194.sL.t = ((40210085547 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0194.sL]
  rw [e0, e1] at h
  exact h

theorem band_0195 : RS5.BandZeros ((40210085547 : ℝ) / 65536) ((40214619325 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0195.s0 RH1E6S10_0195.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0195.s0 RH1E6S10_0195.rest = RH1E6S10_0195.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0195.s0 :: RH1E6S10_0195.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0195.s0.t = ((40210085547 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0195.s0]
  have e1 : RH1E6S10_0195.sL.t = ((40214619325 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0195.sL]
  rw [e0, e1] at h
  exact h

theorem part_024_1 : RS5.BandZeros ((40205506924 : ℝ) / 65536) ((40214619325 : ℝ) / 65536) 254 := by
  have g0 := band_0194
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0195
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((40205506924 : ℝ) / 65536) ((40214619325 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_024_1 <;> assumption
