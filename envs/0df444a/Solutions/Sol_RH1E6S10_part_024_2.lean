-- Prove2me | solution 1 for RH1E6S10.part_024_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T22:23:48.637317+00:00
-- url     : https://prove2.me/submissions/5298c6a0-065e-438d-82e6-f3275e24c474

import Definitions.Def_RH1E6S10_D024_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0196 : RS5.BandZeros ((40214619325 : ℝ) / 65536) ((40219170978 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0196.s0 RH1E6S10_0196.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0196.s0 RH1E6S10_0196.rest = RH1E6S10_0196.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0196.s0 :: RH1E6S10_0196.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0196.s0.t = ((40214619325 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0196.s0]
  have e1 : RH1E6S10_0196.sL.t = ((40219170978 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0196.sL]
  rw [e0, e1] at h
  exact h

theorem band_0197 : RS5.BandZeros ((40219170978 : ℝ) / 65536) ((40223722586 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0197.s0 RH1E6S10_0197.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0197.s0 RH1E6S10_0197.rest = RH1E6S10_0197.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0197.s0 :: RH1E6S10_0197.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0197.s0.t = ((40219170978 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0197.s0]
  have e1 : RH1E6S10_0197.sL.t = ((40223722586 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0197.sL]
  rw [e0, e1] at h
  exact h

theorem part_024_2 : RS5.BandZeros ((40214619325 : ℝ) / 65536) ((40223722586 : ℝ) / 65536) 254 := by
  have g0 := band_0196
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0197
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((40214619325 : ℝ) / 65536) ((40223722586 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_024_2 <;> assumption
