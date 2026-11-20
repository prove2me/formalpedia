-- Prove2me | solution 1 for RH1E6S01.part_048_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T01:00:02.043685+00:00
-- url     : https://prove2.me/submissions/16c136ce-115d-4962-8575-af22633e42b8

import Definitions.Def_RH1E6S01_D048_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0384 : RS5.BandZeros ((11804030787 : ℝ) / 65536) ((11809136002 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0384.s0 RH1E6S01_0384.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0384.s0 RH1E6S01_0384.rest = RH1E6S01_0384.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0384.s0 :: RH1E6S01_0384.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0384.s0.t = ((11804030787 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0384.s0]
  have e1 : RH1E6S01_0384.sL.t = ((11809136002 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0384.sL]
  rw [e0, e1] at h
  exact h

theorem band_0385 : RS5.BandZeros ((11809136002 : ℝ) / 65536) ((11814241002 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0385.s0 RH1E6S01_0385.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0385.s0 RH1E6S01_0385.rest = RH1E6S01_0385.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0385.s0 :: RH1E6S01_0385.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0385.s0.t = ((11809136002 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0385.s0]
  have e1 : RH1E6S01_0385.sL.t = ((11814241002 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0385.sL]
  rw [e0, e1] at h
  exact h

theorem part_048_0 : RS5.BandZeros ((11804030787 : ℝ) / 65536) ((11814241002 : ℝ) / 65536) 254 := by
  have g0 := band_0384
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0385
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((11804030787 : ℝ) / 65536) ((11814241002 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_048_0 <;> assumption
