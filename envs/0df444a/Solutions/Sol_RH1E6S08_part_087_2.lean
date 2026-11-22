-- Prove2me | solution 1 for RH1E6S08.part_087_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T08:06:22.287601+00:00
-- url     : https://prove2.me/submissions/dfd0a924-0893-49e1-9ba1-e23d21887fb5

import Definitions.Def_RH1E6S08_D087_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0700 : RS5.BandZeros ((35998356422 : ℝ) / 65536) ((36002936914 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0700.s0 RH1E6S08_0700.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0700.s0 RH1E6S08_0700.rest = RH1E6S08_0700.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0700.s0 :: RH1E6S08_0700.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0700.s0.t = ((35998356422 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0700.s0]
  have e1 : RH1E6S08_0700.sL.t = ((36002936914 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0700.sL]
  rw [e0, e1] at h
  exact h

theorem band_0701 : RS5.BandZeros ((36002936914 : ℝ) / 65536) ((36007542408 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0701.s0 RH1E6S08_0701.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0701.s0 RH1E6S08_0701.rest = RH1E6S08_0701.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0701.s0 :: RH1E6S08_0701.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0701.s0.t = ((36002936914 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0701.s0]
  have e1 : RH1E6S08_0701.sL.t = ((36007542408 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0701.sL]
  rw [e0, e1] at h
  exact h

theorem part_087_2 : RS5.BandZeros ((35998356422 : ℝ) / 65536) ((36007542408 : ℝ) / 65536) 254 := by
  have g0 := band_0700
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0701
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((35998356422 : ℝ) / 65536) ((36007542408 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_087_2 <;> assumption
