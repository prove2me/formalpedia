-- Prove2me | solution 1 for RH1E6S12.part_043_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T09:30:11.172569+00:00
-- url     : https://prove2.me/submissions/65f3b637-eebe-4f45-a152-1d9ffd957a68

import Definitions.Def_RH1E6S12_D043_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0346 : RS5.BandZeros ((47429998828 : ℝ) / 65536) ((47434492069 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0346.s0 RH1E6S12_0346.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0346.s0 RH1E6S12_0346.rest = RH1E6S12_0346.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0346.s0 :: RH1E6S12_0346.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0346.s0.t = ((47429998828 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0346.s0]
  have e1 : RH1E6S12_0346.sL.t = ((47434492069 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0346.sL]
  rw [e0, e1] at h
  exact h

theorem band_0347 : RS5.BandZeros ((47434492069 : ℝ) / 65536) ((47438973203 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0347.s0 RH1E6S12_0347.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0347.s0 RH1E6S12_0347.rest = RH1E6S12_0347.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0347.s0 :: RH1E6S12_0347.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0347.s0.t = ((47434492069 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0347.s0]
  have e1 : RH1E6S12_0347.sL.t = ((47438973203 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0347.sL]
  rw [e0, e1] at h
  exact h

theorem part_043_1 : RS5.BandZeros ((47429998828 : ℝ) / 65536) ((47438973203 : ℝ) / 65536) 254 := by
  have g0 := band_0346
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0347
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((47429998828 : ℝ) / 65536) ((47438973203 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_043_1 <;> assumption
