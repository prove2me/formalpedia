-- Prove2me | solution 1 for RH1E6S08.part_005_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T04:11:40.164859+00:00
-- url     : https://prove2.me/submissions/a09b2267-2bfa-43c5-8ecf-afd4831a7eb6

import Definitions.Def_RH1E6S08_D005_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0044 : RS5.BandZeros ((32971877222 : ℝ) / 65536) ((32976500401 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0044.s0 RH1E6S08_0044.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0044.s0 RH1E6S08_0044.rest = RH1E6S08_0044.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0044.s0 :: RH1E6S08_0044.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0044.s0.t = ((32971877222 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0044.s0]
  have e1 : RH1E6S08_0044.sL.t = ((32976500401 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0044.sL]
  rw [e0, e1] at h
  exact h

theorem band_0045 : RS5.BandZeros ((32976500401 : ℝ) / 65536) ((32981129051 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0045.s0 RH1E6S08_0045.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0045.s0 RH1E6S08_0045.rest = RH1E6S08_0045.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0045.s0 :: RH1E6S08_0045.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0045.s0.t = ((32976500401 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0045.s0]
  have e1 : RH1E6S08_0045.sL.t = ((32981129051 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0045.sL]
  rw [e0, e1] at h
  exact h

theorem part_005_2 : RS5.BandZeros ((32971877222 : ℝ) / 65536) ((32981129051 : ℝ) / 65536) 254 := by
  have g0 := band_0044
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0045
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((32971877222 : ℝ) / 65536) ((32981129051 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_005_2 <;> assumption
