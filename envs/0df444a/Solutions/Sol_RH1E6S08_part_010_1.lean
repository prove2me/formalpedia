-- Prove2me | solution 1 for RH1E6S08.part_010_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T04:25:48.994549+00:00
-- url     : https://prove2.me/submissions/78566c33-def1-404f-b1bc-f6d77828d8b2

import Definitions.Def_RH1E6S08_D010_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0082 : RS5.BandZeros ((33147856091 : ℝ) / 65536) ((33152480613 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0082.s0 RH1E6S08_0082.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0082.s0 RH1E6S08_0082.rest = RH1E6S08_0082.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0082.s0 :: RH1E6S08_0082.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0082.s0.t = ((33147856091 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0082.s0]
  have e1 : RH1E6S08_0082.sL.t = ((33152480613 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0082.sL]
  rw [e0, e1] at h
  exact h

theorem band_0083 : RS5.BandZeros ((33152480613 : ℝ) / 65536) ((33157085299 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0083.s0 RH1E6S08_0083.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0083.s0 RH1E6S08_0083.rest = RH1E6S08_0083.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0083.s0 :: RH1E6S08_0083.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0083.s0.t = ((33152480613 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0083.s0]
  have e1 : RH1E6S08_0083.sL.t = ((33157085299 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0083.sL]
  rw [e0, e1] at h
  exact h

theorem part_010_1 : RS5.BandZeros ((33147856091 : ℝ) / 65536) ((33157085299 : ℝ) / 65536) 254 := by
  have g0 := band_0082
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0083
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((33147856091 : ℝ) / 65536) ((33157085299 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_010_1 <;> assumption
