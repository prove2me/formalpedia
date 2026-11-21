-- Prove2me | solution 1 for RH1E6S08.part_037_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T05:46:33.883339+00:00
-- url     : https://prove2.me/submissions/566135cd-7167-4170-a875-3eb75d57a2a0

import Definitions.Def_RH1E6S08_D037_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0296 : RS5.BandZeros ((34137267344 : ℝ) / 65536) ((34141887867 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0296.s0 RH1E6S08_0296.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0296.s0 RH1E6S08_0296.rest = RH1E6S08_0296.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0296.s0 :: RH1E6S08_0296.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0296.s0.t = ((34137267344 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0296.s0]
  have e1 : RH1E6S08_0296.sL.t = ((34141887867 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0296.sL]
  rw [e0, e1] at h
  exact h

theorem band_0297 : RS5.BandZeros ((34141887867 : ℝ) / 65536) ((34146505307 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0297.s0 RH1E6S08_0297.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0297.s0 RH1E6S08_0297.rest = RH1E6S08_0297.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0297.s0 :: RH1E6S08_0297.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0297.s0.t = ((34141887867 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0297.s0]
  have e1 : RH1E6S08_0297.sL.t = ((34146505307 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0297.sL]
  rw [e0, e1] at h
  exact h

theorem part_037_0 : RS5.BandZeros ((34137267344 : ℝ) / 65536) ((34146505307 : ℝ) / 65536) 254 := by
  have g0 := band_0296
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0297
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((34137267344 : ℝ) / 65536) ((34146505307 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_037_0 <;> assumption
