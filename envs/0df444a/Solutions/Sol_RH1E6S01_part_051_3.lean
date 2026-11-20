-- Prove2me | solution 1 for RH1E6S01.part_051_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T01:09:17.865174+00:00
-- url     : https://prove2.me/submissions/2be3935a-db72-47fd-8e54-948b2d8788d2

import Definitions.Def_RH1E6S01_D051_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0414 : RS5.BandZeros ((11956803671 : ℝ) / 65536) ((11961882465 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0414.s0 RH1E6S01_0414.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0414.s0 RH1E6S01_0414.rest = RH1E6S01_0414.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0414.s0 :: RH1E6S01_0414.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0414.s0.t = ((11956803671 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0414.s0]
  have e1 : RH1E6S01_0414.sL.t = ((11961882465 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0414.sL]
  rw [e0, e1] at h
  exact h

theorem band_0415 : RS5.BandZeros ((11961882465 : ℝ) / 65536) ((11966981082 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0415.s0 RH1E6S01_0415.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0415.s0 RH1E6S01_0415.rest = RH1E6S01_0415.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0415.s0 :: RH1E6S01_0415.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0415.s0.t = ((11961882465 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0415.s0]
  have e1 : RH1E6S01_0415.sL.t = ((11966981082 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0415.sL]
  rw [e0, e1] at h
  exact h

theorem part_051_3 : RS5.BandZeros ((11956803671 : ℝ) / 65536) ((11966981082 : ℝ) / 65536) 254 := by
  have g0 := band_0414
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0415
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((11956803671 : ℝ) / 65536) ((11966981082 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_051_3 <;> assumption
