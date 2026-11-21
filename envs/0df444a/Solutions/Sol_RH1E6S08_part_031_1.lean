-- Prove2me | solution 1 for RH1E6S08.part_031_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T05:22:05.662481+00:00
-- url     : https://prove2.me/submissions/a700e586-c4aa-4a81-9749-20e3e3cf198d

import Definitions.Def_RH1E6S08_D031_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0250 : RS5.BandZeros ((33924824004 : ℝ) / 65536) ((33929419684 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0250.s0 RH1E6S08_0250.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0250.s0 RH1E6S08_0250.rest = RH1E6S08_0250.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0250.s0 :: RH1E6S08_0250.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0250.s0.t = ((33924824004 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0250.s0]
  have e1 : RH1E6S08_0250.sL.t = ((33929419684 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0250.sL]
  rw [e0, e1] at h
  exact h

theorem band_0251 : RS5.BandZeros ((33929419684 : ℝ) / 65536) ((33934027654 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0251.s0 RH1E6S08_0251.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0251.s0 RH1E6S08_0251.rest = RH1E6S08_0251.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0251.s0 :: RH1E6S08_0251.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0251.s0.t = ((33929419684 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0251.s0]
  have e1 : RH1E6S08_0251.sL.t = ((33934027654 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0251.sL]
  rw [e0, e1] at h
  exact h

theorem part_031_1 : RS5.BandZeros ((33924824004 : ℝ) / 65536) ((33934027654 : ℝ) / 65536) 254 := by
  have g0 := band_0250
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0251
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((33924824004 : ℝ) / 65536) ((33934027654 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_031_1 <;> assumption
