-- Prove2me | solution 1 for RH1E6S08.part_073_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T07:27:56.522299+00:00
-- url     : https://prove2.me/submissions/6ec4f40d-acea-4307-8ad9-0496e5280250

import Definitions.Def_RH1E6S08_D073_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0588 : RS5.BandZeros ((35483280653 : ℝ) / 65536) ((35487877475 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0588.s0 RH1E6S08_0588.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0588.s0 RH1E6S08_0588.rest = RH1E6S08_0588.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0588.s0 :: RH1E6S08_0588.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0588.s0.t = ((35483280653 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0588.s0]
  have e1 : RH1E6S08_0588.sL.t = ((35487877475 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0588.sL]
  rw [e0, e1] at h
  exact h

theorem band_0589 : RS5.BandZeros ((35487877475 : ℝ) / 65536) ((35492471830 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0589.s0 RH1E6S08_0589.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0589.s0 RH1E6S08_0589.rest = RH1E6S08_0589.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0589.s0 :: RH1E6S08_0589.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0589.s0.t = ((35487877475 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0589.s0]
  have e1 : RH1E6S08_0589.sL.t = ((35492471830 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0589.sL]
  rw [e0, e1] at h
  exact h

theorem part_073_2 : RS5.BandZeros ((35483280653 : ℝ) / 65536) ((35492471830 : ℝ) / 65536) 254 := by
  have g0 := band_0588
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0589
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((35483280653 : ℝ) / 65536) ((35492471830 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_073_2 <;> assumption
