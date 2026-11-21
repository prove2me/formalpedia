-- Prove2me | solution 1 for RH1E6S08.part_023_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T05:00:06.425433+00:00
-- url     : https://prove2.me/submissions/9a0baa51-2d8b-47be-87cc-8b091ebedb8d

import Definitions.Def_RH1E6S08_D023_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0188 : RS5.BandZeros ((33638248793 : ℝ) / 65536) ((33642869532 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0188.s0 RH1E6S08_0188.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0188.s0 RH1E6S08_0188.rest = RH1E6S08_0188.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0188.s0 :: RH1E6S08_0188.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0188.s0.t = ((33638248793 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0188.s0]
  have e1 : RH1E6S08_0188.sL.t = ((33642869532 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0188.sL]
  rw [e0, e1] at h
  exact h

theorem band_0189 : RS5.BandZeros ((33642869532 : ℝ) / 65536) ((33647505137 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0189.s0 RH1E6S08_0189.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0189.s0 RH1E6S08_0189.rest = RH1E6S08_0189.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0189.s0 :: RH1E6S08_0189.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0189.s0.t = ((33642869532 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0189.s0]
  have e1 : RH1E6S08_0189.sL.t = ((33647505137 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0189.sL]
  rw [e0, e1] at h
  exact h

theorem part_023_2 : RS5.BandZeros ((33638248793 : ℝ) / 65536) ((33647505137 : ℝ) / 65536) 254 := by
  have g0 := band_0188
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0189
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((33638248793 : ℝ) / 65536) ((33647505137 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_023_2 <;> assumption
