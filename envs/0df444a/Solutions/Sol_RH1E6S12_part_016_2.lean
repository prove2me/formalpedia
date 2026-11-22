-- Prove2me | solution 1 for RH1E6S12.part_016_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T08:14:14.469745+00:00
-- url     : https://prove2.me/submissions/ae7dbee8-975b-4bcc-b5a1-5a628378f876

import Definitions.Def_RH1E6S12_D016_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0132 : RS5.BandZeros ((46468896338 : ℝ) / 65536) ((46473392511 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0132.s0 RH1E6S12_0132.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0132.s0 RH1E6S12_0132.rest = RH1E6S12_0132.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0132.s0 :: RH1E6S12_0132.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0132.s0.t = ((46468896338 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0132.s0]
  have e1 : RH1E6S12_0132.sL.t = ((46473392511 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0132.sL]
  rw [e0, e1] at h
  exact h

theorem band_0133 : RS5.BandZeros ((46473392511 : ℝ) / 65536) ((46477881814 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0133.s0 RH1E6S12_0133.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0133.s0 RH1E6S12_0133.rest = RH1E6S12_0133.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0133.s0 :: RH1E6S12_0133.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0133.s0.t = ((46473392511 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0133.s0]
  have e1 : RH1E6S12_0133.sL.t = ((46477881814 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0133.sL]
  rw [e0, e1] at h
  exact h

theorem part_016_2 : RS5.BandZeros ((46468896338 : ℝ) / 65536) ((46477881814 : ℝ) / 65536) 254 := by
  have g0 := band_0132
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0133
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((46468896338 : ℝ) / 65536) ((46477881814 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_016_2 <;> assumption
