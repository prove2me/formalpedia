-- Prove2me | solution 1 for RH1E6S08.part_071_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T07:22:04.61174+00:00
-- url     : https://prove2.me/submissions/9e656572-4d44-416c-9ebe-89c2909158e1

import Definitions.Def_RH1E6S08_D071_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0574 : RS5.BandZeros ((35418860953 : ℝ) / 65536) ((35423437213 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0574.s0 RH1E6S08_0574.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0574.s0 RH1E6S08_0574.rest = RH1E6S08_0574.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0574.s0 :: RH1E6S08_0574.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0574.s0.t = ((35418860953 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0574.s0]
  have e1 : RH1E6S08_0574.sL.t = ((35423437213 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0574.sL]
  rw [e0, e1] at h
  exact h

theorem band_0575 : RS5.BandZeros ((35423437213 : ℝ) / 65536) ((35428039680 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0575.s0 RH1E6S08_0575.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0575.s0 RH1E6S08_0575.rest = RH1E6S08_0575.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0575.s0 :: RH1E6S08_0575.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0575.s0.t = ((35423437213 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0575.s0]
  have e1 : RH1E6S08_0575.sL.t = ((35428039680 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0575.sL]
  rw [e0, e1] at h
  exact h

theorem part_071_3 : RS5.BandZeros ((35418860953 : ℝ) / 65536) ((35428039680 : ℝ) / 65536) 254 := by
  have g0 := band_0574
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0575
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((35418860953 : ℝ) / 65536) ((35428039680 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_071_3 <;> assumption
