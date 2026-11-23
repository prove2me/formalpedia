-- Prove2me | solution 1 for RH1E6S15.part_063_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T11:40:16.769681+00:00
-- url     : https://prove2.me/submissions/b338660a-4612-4f84-be4d-c4b1f34535a2

import Definitions.Def_RH1E6S15_D063_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0506 : RS5.BandZeros ((57941443395 : ℝ) / 65536) ((57945873370 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0506.s0 RH1E6S15_0506.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0506.s0 RH1E6S15_0506.rest = RH1E6S15_0506.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0506.s0 :: RH1E6S15_0506.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0506.s0.t = ((57941443395 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0506.s0]
  have e1 : RH1E6S15_0506.sL.t = ((57945873370 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0506.sL]
  rw [e0, e1] at h
  exact h

theorem band_0507 : RS5.BandZeros ((57945873370 : ℝ) / 65536) ((57950254156 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0507.s0 RH1E6S15_0507.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0507.s0 RH1E6S15_0507.rest = RH1E6S15_0507.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0507.s0 :: RH1E6S15_0507.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0507.s0.t = ((57945873370 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0507.s0]
  have e1 : RH1E6S15_0507.sL.t = ((57950254156 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0507.sL]
  rw [e0, e1] at h
  exact h

theorem part_063_1 : RS5.BandZeros ((57941443395 : ℝ) / 65536) ((57950254156 : ℝ) / 65536) 254 := by
  have g0 := band_0506
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0507
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((57941443395 : ℝ) / 65536) ((57950254156 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_063_1 <;> assumption
