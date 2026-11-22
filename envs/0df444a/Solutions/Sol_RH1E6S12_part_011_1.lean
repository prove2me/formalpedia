-- Prove2me | solution 1 for RH1E6S12.part_011_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T07:56:52.440099+00:00
-- url     : https://prove2.me/submissions/922ba21d-6483-4fc7-99d2-2c5e09f4b5ed

import Definitions.Def_RH1E6S12_D011_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0090 : RS5.BandZeros ((46280066158 : ℝ) / 65536) ((46284560260 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0090.s0 RH1E6S12_0090.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0090.s0 RH1E6S12_0090.rest = RH1E6S12_0090.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0090.s0 :: RH1E6S12_0090.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0090.s0.t = ((46280066158 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0090.s0]
  have e1 : RH1E6S12_0090.sL.t = ((46284560260 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0090.sL]
  rw [e0, e1] at h
  exact h

theorem band_0091 : RS5.BandZeros ((46284560260 : ℝ) / 65536) ((46289059203 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0091.s0 RH1E6S12_0091.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0091.s0 RH1E6S12_0091.rest = RH1E6S12_0091.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0091.s0 :: RH1E6S12_0091.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0091.s0.t = ((46284560260 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0091.s0]
  have e1 : RH1E6S12_0091.sL.t = ((46289059203 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0091.sL]
  rw [e0, e1] at h
  exact h

theorem part_011_1 : RS5.BandZeros ((46280066158 : ℝ) / 65536) ((46289059203 : ℝ) / 65536) 254 := by
  have g0 := band_0090
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0091
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((46280066158 : ℝ) / 65536) ((46289059203 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_011_1 <;> assumption
