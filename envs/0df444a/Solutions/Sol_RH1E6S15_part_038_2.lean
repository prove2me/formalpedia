-- Prove2me | solution 1 for RH1E6S15.part_038_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T10:08:46.029733+00:00
-- url     : https://prove2.me/submissions/58b19875-f75b-4fa4-99b9-10b9734ba0e2

import Definitions.Def_RH1E6S15_D038_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0308 : RS5.BandZeros ((57067421461 : ℝ) / 65536) ((57071838031 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0308.s0 RH1E6S15_0308.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0308.s0 RH1E6S15_0308.rest = RH1E6S15_0308.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0308.s0 :: RH1E6S15_0308.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0308.s0.t = ((57067421461 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0308.s0]
  have e1 : RH1E6S15_0308.sL.t = ((57071838031 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0308.sL]
  rw [e0, e1] at h
  exact h

theorem band_0309 : RS5.BandZeros ((57071838031 : ℝ) / 65536) ((57076258578 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0309.s0 RH1E6S15_0309.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0309.s0 RH1E6S15_0309.rest = RH1E6S15_0309.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0309.s0 :: RH1E6S15_0309.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0309.s0.t = ((57071838031 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0309.s0]
  have e1 : RH1E6S15_0309.sL.t = ((57076258578 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0309.sL]
  rw [e0, e1] at h
  exact h

theorem part_038_2 : RS5.BandZeros ((57067421461 : ℝ) / 65536) ((57076258578 : ℝ) / 65536) 254 := by
  have g0 := band_0308
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0309
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((57067421461 : ℝ) / 65536) ((57076258578 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_038_2 <;> assumption
