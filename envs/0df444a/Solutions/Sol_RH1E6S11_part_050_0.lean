-- Prove2me | solution 1 for RH1E6S11.part_050_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T05:22:01.145364+00:00
-- url     : https://prove2.me/submissions/c5737951-b93f-408f-9ea7-2f4fe4dd9606

import Definitions.Def_RH1E6S11_D050_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0400 : RS5.BandZeros ((44406700304 : ℝ) / 65536) ((44411221896 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0400.s0 RH1E6S11_0400.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0400.s0 RH1E6S11_0400.rest = RH1E6S11_0400.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0400.s0 :: RH1E6S11_0400.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0400.s0.t = ((44406700304 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0400.s0]
  have e1 : RH1E6S11_0400.sL.t = ((44411221896 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0400.sL]
  rw [e0, e1] at h
  exact h

theorem band_0401 : RS5.BandZeros ((44411221896 : ℝ) / 65536) ((44415716798 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0401.s0 RH1E6S11_0401.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0401.s0 RH1E6S11_0401.rest = RH1E6S11_0401.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0401.s0 :: RH1E6S11_0401.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0401.s0.t = ((44411221896 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0401.s0]
  have e1 : RH1E6S11_0401.sL.t = ((44415716798 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0401.sL]
  rw [e0, e1] at h
  exact h

theorem part_050_0 : RS5.BandZeros ((44406700304 : ℝ) / 65536) ((44415716798 : ℝ) / 65536) 254 := by
  have g0 := band_0400
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0401
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((44406700304 : ℝ) / 65536) ((44415716798 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_050_0 <;> assumption
