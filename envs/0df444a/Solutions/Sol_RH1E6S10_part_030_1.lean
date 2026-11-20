-- Prove2me | solution 1 for RH1E6S10.part_030_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T19:38:20.933144+00:00
-- url     : https://prove2.me/submissions/5d2768c8-54f8-4cc1-a5cd-68bd88451e9f

import Definitions.Def_RH1E6S10_D030_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0242 : RS5.BandZeros ((40423940105 : ℝ) / 65536) ((40428489702 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0242.s0 RH1E6S10_0242.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0242.s0 RH1E6S10_0242.rest = RH1E6S10_0242.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0242.s0 :: RH1E6S10_0242.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0242.s0.t = ((40423940105 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0242.s0]
  have e1 : RH1E6S10_0242.sL.t = ((40428489702 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0242.sL]
  rw [e0, e1] at h
  exact h

theorem band_0243 : RS5.BandZeros ((40428489702 : ℝ) / 65536) ((40433057167 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0243.s0 RH1E6S10_0243.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0243.s0 RH1E6S10_0243.rest = RH1E6S10_0243.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0243.s0 :: RH1E6S10_0243.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0243.s0.t = ((40428489702 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0243.s0]
  have e1 : RH1E6S10_0243.sL.t = ((40433057167 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0243.sL]
  rw [e0, e1] at h
  exact h

theorem part_030_1 : RS5.BandZeros ((40423940105 : ℝ) / 65536) ((40433057167 : ℝ) / 65536) 254 := by
  have g0 := band_0242
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0243
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((40423940105 : ℝ) / 65536) ((40433057167 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_030_1 <;> assumption
