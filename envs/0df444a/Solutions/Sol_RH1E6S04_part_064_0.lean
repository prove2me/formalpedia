-- Prove2me | solution 1 for RH1E6S04.part_064_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T10:48:03.681182+00:00
-- url     : https://prove2.me/submissions/0f56037e-abfe-45e7-b2c3-3a36167ee9f0

import Definitions.Def_RH1E6S04_D064_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0512 : RS5.BandZeros ((22132199986 : ℝ) / 65536) ((22137010626 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0512.s0 RH1E6S04_0512.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0512.s0 RH1E6S04_0512.rest = RH1E6S04_0512.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0512.s0 :: RH1E6S04_0512.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0512.s0.t = ((22132199986 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0512.s0]
  have e1 : RH1E6S04_0512.sL.t = ((22137010626 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0512.sL]
  rw [e0, e1] at h
  exact h

theorem band_0513 : RS5.BandZeros ((22137010626 : ℝ) / 65536) ((22141811720 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0513.s0 RH1E6S04_0513.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0513.s0 RH1E6S04_0513.rest = RH1E6S04_0513.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0513.s0 :: RH1E6S04_0513.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0513.s0.t = ((22137010626 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0513.s0]
  have e1 : RH1E6S04_0513.sL.t = ((22141811720 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0513.sL]
  rw [e0, e1] at h
  exact h

theorem part_064_0 : RS5.BandZeros ((22132199986 : ℝ) / 65536) ((22141811720 : ℝ) / 65536) 254 := by
  have g0 := band_0512
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0513
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((22132199986 : ℝ) / 65536) ((22141811720 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_064_0 <;> assumption
