-- Prove2me | solution 1 for RH1E6S16.part_085_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T19:06:07.513802+00:00
-- url     : https://prove2.me/submissions/d3099d06-cdb3-4179-8cd0-b7cfda89b205

import Definitions.Def_RH1E6S16_D085_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0682 : RS5.BandZeros ((61980182847 : ℝ) / 65536) ((61984567337 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0682.s0 RH1E6S16_0682.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0682.s0 RH1E6S16_0682.rest = RH1E6S16_0682.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0682.s0 :: RH1E6S16_0682.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0682.s0.t = ((61980182847 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0682.s0]
  have e1 : RH1E6S16_0682.sL.t = ((61984567337 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0682.sL]
  rw [e0, e1] at h
  exact h

theorem band_0683 : RS5.BandZeros ((61984567337 : ℝ) / 65536) ((61988959291 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0683.s0 RH1E6S16_0683.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0683.s0 RH1E6S16_0683.rest = RH1E6S16_0683.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0683.s0 :: RH1E6S16_0683.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0683.s0.t = ((61984567337 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0683.s0]
  have e1 : RH1E6S16_0683.sL.t = ((61988959291 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0683.sL]
  rw [e0, e1] at h
  exact h

theorem part_085_1 : RS5.BandZeros ((61980182847 : ℝ) / 65536) ((61988959291 : ℝ) / 65536) 254 := by
  have g0 := band_0682
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0683
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((61980182847 : ℝ) / 65536) ((61988959291 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_085_1 <;> assumption
