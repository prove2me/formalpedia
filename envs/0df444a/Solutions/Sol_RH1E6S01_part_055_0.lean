-- Prove2me | solution 1 for RH1E6S01.part_055_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T01:14:14.209183+00:00
-- url     : https://prove2.me/submissions/5e74f0d2-191b-4b2e-9dc3-06a67e9a31be

import Definitions.Def_RH1E6S01_D055_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0440 : RS5.BandZeros ((12089034583 : ℝ) / 65536) ((12094137967 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0440.s0 RH1E6S01_0440.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0440.s0 RH1E6S01_0440.rest = RH1E6S01_0440.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0440.s0 :: RH1E6S01_0440.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0440.s0.t = ((12089034583 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0440.s0]
  have e1 : RH1E6S01_0440.sL.t = ((12094137967 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0440.sL]
  rw [e0, e1] at h
  exact h

theorem band_0441 : RS5.BandZeros ((12094137967 : ℝ) / 65536) ((12099201118 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0441.s0 RH1E6S01_0441.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0441.s0 RH1E6S01_0441.rest = RH1E6S01_0441.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0441.s0 :: RH1E6S01_0441.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0441.s0.t = ((12094137967 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0441.s0]
  have e1 : RH1E6S01_0441.sL.t = ((12099201118 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0441.sL]
  rw [e0, e1] at h
  exact h

theorem part_055_0 : RS5.BandZeros ((12089034583 : ℝ) / 65536) ((12099201118 : ℝ) / 65536) 254 := by
  have g0 := band_0440
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0441
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((12089034583 : ℝ) / 65536) ((12099201118 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_055_0 <;> assumption
