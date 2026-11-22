-- Prove2me | solution 1 for RH1E6S12.part_017_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T08:17:05.744481+00:00
-- url     : https://prove2.me/submissions/9964e7a7-39bb-424f-b634-0453e3c95035

import Definitions.Def_RH1E6S12_D017_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0138 : RS5.BandZeros ((46495870544 : ℝ) / 65536) ((46500359794 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0138.s0 RH1E6S12_0138.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0138.s0 RH1E6S12_0138.rest = RH1E6S12_0138.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0138.s0 :: RH1E6S12_0138.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0138.s0.t = ((46495870544 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0138.s0]
  have e1 : RH1E6S12_0138.sL.t = ((46500359794 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0138.sL]
  rw [e0, e1] at h
  exact h

theorem band_0139 : RS5.BandZeros ((46500359794 : ℝ) / 65536) ((46504869109 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0139.s0 RH1E6S12_0139.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0139.s0 RH1E6S12_0139.rest = RH1E6S12_0139.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0139.s0 :: RH1E6S12_0139.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0139.s0.t = ((46500359794 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0139.s0]
  have e1 : RH1E6S12_0139.sL.t = ((46504869109 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0139.sL]
  rw [e0, e1] at h
  exact h

theorem part_017_1 : RS5.BandZeros ((46495870544 : ℝ) / 65536) ((46504869109 : ℝ) / 65536) 254 := by
  have g0 := band_0138
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0139
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((46495870544 : ℝ) / 65536) ((46504869109 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_017_1 <;> assumption
