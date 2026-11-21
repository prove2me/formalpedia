-- Prove2me | solution 1 for RH1E6S08.part_008_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T04:17:36.598174+00:00
-- url     : https://prove2.me/submissions/4d9a7b98-ef60-45d5-aedb-482dc8b7689f

import Definitions.Def_RH1E6S08_D008_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0064 : RS5.BandZeros ((33064491758 : ℝ) / 65536) ((33069127243 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0064.s0 RH1E6S08_0064.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0064.s0 RH1E6S08_0064.rest = RH1E6S08_0064.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0064.s0 :: RH1E6S08_0064.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0064.s0.t = ((33064491758 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0064.s0]
  have e1 : RH1E6S08_0064.sL.t = ((33069127243 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0064.sL]
  rw [e0, e1] at h
  exact h

theorem band_0065 : RS5.BandZeros ((33069127243 : ℝ) / 65536) ((33073754574 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0065.s0 RH1E6S08_0065.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0065.s0 RH1E6S08_0065.rest = RH1E6S08_0065.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0065.s0 :: RH1E6S08_0065.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0065.s0.t = ((33069127243 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0065.s0]
  have e1 : RH1E6S08_0065.sL.t = ((33073754574 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0065.sL]
  rw [e0, e1] at h
  exact h

theorem part_008_0 : RS5.BandZeros ((33064491758 : ℝ) / 65536) ((33073754574 : ℝ) / 65536) 254 := by
  have g0 := band_0064
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0065
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((33064491758 : ℝ) / 65536) ((33073754574 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_008_0 <;> assumption
