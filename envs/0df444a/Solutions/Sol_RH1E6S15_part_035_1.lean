-- Prove2me | solution 1 for RH1E6S15.part_035_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T09:54:01.136285+00:00
-- url     : https://prove2.me/submissions/7f8cf023-6a76-4025-9528-dac8c45db0ad

import Definitions.Def_RH1E6S15_D035_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0282 : RS5.BandZeros ((56952574871 : ℝ) / 65536) ((56956966634 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0282.s0 RH1E6S15_0282.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0282.s0 RH1E6S15_0282.rest = RH1E6S15_0282.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0282.s0 :: RH1E6S15_0282.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0282.s0.t = ((56952574871 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0282.s0]
  have e1 : RH1E6S15_0282.sL.t = ((56956966634 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0282.sL]
  rw [e0, e1] at h
  exact h

theorem band_0283 : RS5.BandZeros ((56956966634 : ℝ) / 65536) ((56961406385 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0283.s0 RH1E6S15_0283.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0283.s0 RH1E6S15_0283.rest = RH1E6S15_0283.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0283.s0 :: RH1E6S15_0283.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0283.s0.t = ((56956966634 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0283.s0]
  have e1 : RH1E6S15_0283.sL.t = ((56961406385 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0283.sL]
  rw [e0, e1] at h
  exact h

theorem part_035_1 : RS5.BandZeros ((56952574871 : ℝ) / 65536) ((56961406385 : ℝ) / 65536) 254 := by
  have g0 := band_0282
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0283
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((56952574871 : ℝ) / 65536) ((56961406385 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_035_1 <;> assumption
