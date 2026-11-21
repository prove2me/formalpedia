-- Prove2me | solution 1 for RH1E6S08.part_023_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T05:00:04.398166+00:00
-- url     : https://prove2.me/submissions/c9fad208-3e0a-47d4-96e4-7da6144256d9

import Definitions.Def_RH1E6S08_D023_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0186 : RS5.BandZeros ((33629015328 : ℝ) / 65536) ((33633648907 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0186.s0 RH1E6S08_0186.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0186.s0 RH1E6S08_0186.rest = RH1E6S08_0186.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0186.s0 :: RH1E6S08_0186.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0186.s0.t = ((33629015328 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0186.s0]
  have e1 : RH1E6S08_0186.sL.t = ((33633648907 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0186.sL]
  rw [e0, e1] at h
  exact h

theorem band_0187 : RS5.BandZeros ((33633648907 : ℝ) / 65536) ((33638248793 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0187.s0 RH1E6S08_0187.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0187.s0 RH1E6S08_0187.rest = RH1E6S08_0187.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0187.s0 :: RH1E6S08_0187.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0187.s0.t = ((33633648907 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0187.s0]
  have e1 : RH1E6S08_0187.sL.t = ((33638248793 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0187.sL]
  rw [e0, e1] at h
  exact h

theorem part_023_1 : RS5.BandZeros ((33629015328 : ℝ) / 65536) ((33638248793 : ℝ) / 65536) 254 := by
  have g0 := band_0186
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0187
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((33629015328 : ℝ) / 65536) ((33638248793 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_023_1 <;> assumption
