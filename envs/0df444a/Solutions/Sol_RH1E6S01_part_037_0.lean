-- Prove2me | solution 1 for RH1E6S01.part_037_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T00:38:38.922055+00:00
-- url     : https://prove2.me/submissions/a39f8bc9-6872-4c8d-b2c4-c81f16736420

import Definitions.Def_RH1E6S01_D037_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0296 : RS5.BandZeros ((11354801425 : ℝ) / 65536) ((11359936076 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0296.s0 RH1E6S01_0296.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0296.s0 RH1E6S01_0296.rest = RH1E6S01_0296.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0296.s0 :: RH1E6S01_0296.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0296.s0.t = ((11354801425 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0296.s0]
  have e1 : RH1E6S01_0296.sL.t = ((11359936076 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0296.sL]
  rw [e0, e1] at h
  exact h

theorem band_0297 : RS5.BandZeros ((11359936076 : ℝ) / 65536) ((11365030230 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0297.s0 RH1E6S01_0297.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0297.s0 RH1E6S01_0297.rest = RH1E6S01_0297.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0297.s0 :: RH1E6S01_0297.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0297.s0.t = ((11359936076 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0297.s0]
  have e1 : RH1E6S01_0297.sL.t = ((11365030230 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0297.sL]
  rw [e0, e1] at h
  exact h

theorem part_037_0 : RS5.BandZeros ((11354801425 : ℝ) / 65536) ((11365030230 : ℝ) / 65536) 254 := by
  have g0 := band_0296
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0297
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((11354801425 : ℝ) / 65536) ((11365030230 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_037_0 <;> assumption
