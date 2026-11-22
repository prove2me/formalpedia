-- Prove2me | solution 1 for RH1E6S12.part_012_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T08:00:06.217806+00:00
-- url     : https://prove2.me/submissions/319fa6d5-e798-421e-b8fe-28756b4397ae

import Definitions.Def_RH1E6S12_D012_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0098 : RS5.BandZeros ((46316044187 : ℝ) / 65536) ((46320546947 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0098.s0 RH1E6S12_0098.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0098.s0 RH1E6S12_0098.rest = RH1E6S12_0098.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0098.s0 :: RH1E6S12_0098.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0098.s0.t = ((46316044187 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0098.s0]
  have e1 : RH1E6S12_0098.sL.t = ((46320546947 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0098.sL]
  rw [e0, e1] at h
  exact h

theorem band_0099 : RS5.BandZeros ((46320546947 : ℝ) / 65536) ((46325031379 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0099.s0 RH1E6S12_0099.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0099.s0 RH1E6S12_0099.rest = RH1E6S12_0099.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0099.s0 :: RH1E6S12_0099.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0099.s0.t = ((46320546947 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0099.s0]
  have e1 : RH1E6S12_0099.sL.t = ((46325031379 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0099.sL]
  rw [e0, e1] at h
  exact h

theorem part_012_1 : RS5.BandZeros ((46316044187 : ℝ) / 65536) ((46325031379 : ℝ) / 65536) 254 := by
  have g0 := band_0098
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0099
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((46316044187 : ℝ) / 65536) ((46325031379 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_012_1 <;> assumption
