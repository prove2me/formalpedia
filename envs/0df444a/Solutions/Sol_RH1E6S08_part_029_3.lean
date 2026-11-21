-- Prove2me | solution 1 for RH1E6S08.part_029_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T05:19:07.371197+00:00
-- url     : https://prove2.me/submissions/7a1f8a52-3ad1-4495-96dc-cc9381048535

import Definitions.Def_RH1E6S08_D029_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0238 : RS5.BandZeros ((33869357585 : ℝ) / 65536) ((33873981681 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0238.s0 RH1E6S08_0238.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0238.s0 RH1E6S08_0238.rest = RH1E6S08_0238.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0238.s0 :: RH1E6S08_0238.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0238.s0.t = ((33869357585 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0238.s0]
  have e1 : RH1E6S08_0238.sL.t = ((33873981681 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0238.sL]
  rw [e0, e1] at h
  exact h

theorem band_0239 : RS5.BandZeros ((33873981681 : ℝ) / 65536) ((33878593240 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0239.s0 RH1E6S08_0239.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0239.s0 RH1E6S08_0239.rest = RH1E6S08_0239.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0239.s0 :: RH1E6S08_0239.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0239.s0.t = ((33873981681 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0239.s0]
  have e1 : RH1E6S08_0239.sL.t = ((33878593240 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0239.sL]
  rw [e0, e1] at h
  exact h

theorem part_029_3 : RS5.BandZeros ((33869357585 : ℝ) / 65536) ((33878593240 : ℝ) / 65536) 254 := by
  have g0 := band_0238
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0239
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((33869357585 : ℝ) / 65536) ((33878593240 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_029_3 <;> assumption
