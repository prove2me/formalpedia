-- Prove2me | solution 1 for RH1E6S08.part_045_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T06:10:55.518808+00:00
-- url     : https://prove2.me/submissions/604f9633-cc18-4b7e-b41b-51616249b527

import Definitions.Def_RH1E6S08_D045_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0364 : RS5.BandZeros ((34451140227 : ℝ) / 65536) ((34455736032 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0364.s0 RH1E6S08_0364.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0364.s0 RH1E6S08_0364.rest = RH1E6S08_0364.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0364.s0 :: RH1E6S08_0364.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0364.s0.t = ((34451140227 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0364.s0]
  have e1 : RH1E6S08_0364.sL.t = ((34455736032 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0364.sL]
  rw [e0, e1] at h
  exact h

theorem band_0365 : RS5.BandZeros ((34455736032 : ℝ) / 65536) ((34460362401 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0365.s0 RH1E6S08_0365.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0365.s0 RH1E6S08_0365.rest = RH1E6S08_0365.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0365.s0 :: RH1E6S08_0365.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0365.s0.t = ((34455736032 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0365.s0]
  have e1 : RH1E6S08_0365.sL.t = ((34460362401 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0365.sL]
  rw [e0, e1] at h
  exact h

theorem part_045_2 : RS5.BandZeros ((34451140227 : ℝ) / 65536) ((34460362401 : ℝ) / 65536) 254 := by
  have g0 := band_0364
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0365
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((34451140227 : ℝ) / 65536) ((34460362401 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_045_2 <;> assumption
