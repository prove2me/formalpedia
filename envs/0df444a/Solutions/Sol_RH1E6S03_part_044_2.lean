-- Prove2me | solution 1 for RH1E6S03.part_044_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T06:54:56.961542+00:00
-- url     : https://prove2.me/submissions/a03bc6aa-031f-472d-b18c-38cb88817bbe

import Definitions.Def_RH1E6S03_D044_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0356 : RS5.BandZeros ((18133248625 : ℝ) / 65536) ((18138148911 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0356.s0 RH1E6S03_0356.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0356.s0 RH1E6S03_0356.rest = RH1E6S03_0356.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0356.s0 :: RH1E6S03_0356.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0356.s0.t = ((18133248625 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0356.s0]
  have e1 : RH1E6S03_0356.sL.t = ((18138148911 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0356.sL]
  rw [e0, e1] at h
  exact h

theorem band_0357 : RS5.BandZeros ((18138148911 : ℝ) / 65536) ((18143020193 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0357.s0 RH1E6S03_0357.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0357.s0 RH1E6S03_0357.rest = RH1E6S03_0357.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0357.s0 :: RH1E6S03_0357.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0357.s0.t = ((18138148911 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0357.s0]
  have e1 : RH1E6S03_0357.sL.t = ((18143020193 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0357.sL]
  rw [e0, e1] at h
  exact h

theorem part_044_2 : RS5.BandZeros ((18133248625 : ℝ) / 65536) ((18143020193 : ℝ) / 65536) 254 := by
  have g0 := band_0356
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0357
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((18133248625 : ℝ) / 65536) ((18143020193 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_044_2 <;> assumption
