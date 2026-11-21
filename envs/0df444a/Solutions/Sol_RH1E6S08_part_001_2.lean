-- Prove2me | solution 1 for RH1E6S08.part_001_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T04:00:19.876059+00:00
-- url     : https://prove2.me/submissions/6df5cd8c-ccfc-4127-a567-dabbdfcb957e

import Definitions.Def_RH1E6S08_D001_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0012 : RS5.BandZeros ((32823637484 : ℝ) / 65536) ((32828270322 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0012.s0 RH1E6S08_0012.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0012.s0 RH1E6S08_0012.rest = RH1E6S08_0012.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0012.s0 :: RH1E6S08_0012.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0012.s0.t = ((32823637484 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0012.s0]
  have e1 : RH1E6S08_0012.sL.t = ((32828270322 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0012.sL]
  rw [e0, e1] at h
  exact h

theorem band_0013 : RS5.BandZeros ((32828270322 : ℝ) / 65536) ((32832904195 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0013.s0 RH1E6S08_0013.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0013.s0 RH1E6S08_0013.rest = RH1E6S08_0013.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0013.s0 :: RH1E6S08_0013.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0013.s0.t = ((32828270322 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0013.s0]
  have e1 : RH1E6S08_0013.sL.t = ((32832904195 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0013.sL]
  rw [e0, e1] at h
  exact h

theorem part_001_2 : RS5.BandZeros ((32823637484 : ℝ) / 65536) ((32832904195 : ℝ) / 65536) 254 := by
  have g0 := band_0012
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0013
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((32823637484 : ℝ) / 65536) ((32832904195 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_001_2 <;> assumption
