-- Prove2me | solution 1 for RH1E6S12.part_002_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T07:31:04.346799+00:00
-- url     : https://prove2.me/submissions/c7e72557-dd56-4849-bd9a-b08f5c775ae6

import Definitions.Def_RH1E6S12_D002_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0018 : RS5.BandZeros ((45956198752 : ℝ) / 65536) ((45960703839 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0018.s0 RH1E6S12_0018.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0018.s0 RH1E6S12_0018.rest = RH1E6S12_0018.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0018.s0 :: RH1E6S12_0018.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0018.s0.t = ((45956198752 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0018.s0]
  have e1 : RH1E6S12_0018.sL.t = ((45960703839 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0018.sL]
  rw [e0, e1] at h
  exact h

theorem band_0019 : RS5.BandZeros ((45960703839 : ℝ) / 65536) ((45965202708 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0019.s0 RH1E6S12_0019.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0019.s0 RH1E6S12_0019.rest = RH1E6S12_0019.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0019.s0 :: RH1E6S12_0019.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0019.s0.t = ((45960703839 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0019.s0]
  have e1 : RH1E6S12_0019.sL.t = ((45965202708 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0019.sL]
  rw [e0, e1] at h
  exact h

theorem part_002_1 : RS5.BandZeros ((45956198752 : ℝ) / 65536) ((45965202708 : ℝ) / 65536) 254 := by
  have g0 := band_0018
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0019
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((45956198752 : ℝ) / 65536) ((45965202708 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_002_1 <;> assumption
