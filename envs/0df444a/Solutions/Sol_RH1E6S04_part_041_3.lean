-- Prove2me | solution 1 for RH1E6S04.part_041_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T09:57:56.914766+00:00
-- url     : https://prove2.me/submissions/3835632e-ae1d-4dfd-bfd8-e393d68aa6e4

import Definitions.Def_RH1E6S04_D041_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0334 : RS5.BandZeros ((21276058315 : ℝ) / 65536) ((21280876956 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0334.s0 RH1E6S04_0334.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0334.s0 RH1E6S04_0334.rest = RH1E6S04_0334.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0334.s0 :: RH1E6S04_0334.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0334.s0.t = ((21276058315 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0334.s0]
  have e1 : RH1E6S04_0334.sL.t = ((21280876956 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0334.sL]
  rw [e0, e1] at h
  exact h

theorem band_0335 : RS5.BandZeros ((21280876956 : ℝ) / 65536) ((21285686010 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0335.s0 RH1E6S04_0335.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0335.s0 RH1E6S04_0335.rest = RH1E6S04_0335.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0335.s0 :: RH1E6S04_0335.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0335.s0.t = ((21280876956 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0335.s0]
  have e1 : RH1E6S04_0335.sL.t = ((21285686010 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0335.sL]
  rw [e0, e1] at h
  exact h

theorem part_041_3 : RS5.BandZeros ((21276058315 : ℝ) / 65536) ((21285686010 : ℝ) / 65536) 254 := by
  have g0 := band_0334
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0335
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((21276058315 : ℝ) / 65536) ((21285686010 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_041_3 <;> assumption
