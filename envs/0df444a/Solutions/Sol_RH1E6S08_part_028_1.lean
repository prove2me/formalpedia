-- Prove2me | solution 1 for RH1E6S08.part_028_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T05:15:10.865546+00:00
-- url     : https://prove2.me/submissions/479e3e20-3572-434e-822d-df6252b7861f

import Definitions.Def_RH1E6S08_D028_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0226 : RS5.BandZeros ((33813921886 : ℝ) / 65536) ((33818538584 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0226.s0 RH1E6S08_0226.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0226.s0 RH1E6S08_0226.rest = RH1E6S08_0226.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0226.s0 :: RH1E6S08_0226.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0226.s0.t = ((33813921886 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0226.s0]
  have e1 : RH1E6S08_0226.sL.t = ((33818538584 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0226.sL]
  rw [e0, e1] at h
  exact h

theorem band_0227 : RS5.BandZeros ((33818538584 : ℝ) / 65536) ((33823150810 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0227.s0 RH1E6S08_0227.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0227.s0 RH1E6S08_0227.rest = RH1E6S08_0227.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0227.s0 :: RH1E6S08_0227.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0227.s0.t = ((33818538584 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0227.s0]
  have e1 : RH1E6S08_0227.sL.t = ((33823150810 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0227.sL]
  rw [e0, e1] at h
  exact h

theorem part_028_1 : RS5.BandZeros ((33813921886 : ℝ) / 65536) ((33823150810 : ℝ) / 65536) 254 := by
  have g0 := band_0226
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0227
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((33813921886 : ℝ) / 65536) ((33823150810 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_028_1 <;> assumption
