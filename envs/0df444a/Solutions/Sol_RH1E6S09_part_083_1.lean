-- Prove2me | solution 1 for RH1E6S09.part_083_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T16:06:11.334195+00:00
-- url     : https://prove2.me/submissions/2aa2d838-36dc-465b-b391-e537485d766c

import Definitions.Def_RH1E6S09_D083_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0666 : RS5.BandZeros ((39094332038 : ℝ) / 65536) ((39098890661 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0666.s0 RH1E6S09_0666.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0666.s0 RH1E6S09_0666.rest = RH1E6S09_0666.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0666.s0 :: RH1E6S09_0666.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0666.s0.t = ((39094332038 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0666.s0]
  have e1 : RH1E6S09_0666.sL.t = ((39098890661 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0666.sL]
  rw [e0, e1] at h
  exact h

theorem band_0667 : RS5.BandZeros ((39098890661 : ℝ) / 65536) ((39103443024 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0667.s0 RH1E6S09_0667.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0667.s0 RH1E6S09_0667.rest = RH1E6S09_0667.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0667.s0 :: RH1E6S09_0667.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0667.s0.t = ((39098890661 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0667.s0]
  have e1 : RH1E6S09_0667.sL.t = ((39103443024 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0667.sL]
  rw [e0, e1] at h
  exact h

theorem part_083_1 : RS5.BandZeros ((39094332038 : ℝ) / 65536) ((39103443024 : ℝ) / 65536) 254 := by
  have g0 := band_0666
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0667
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((39094332038 : ℝ) / 65536) ((39103443024 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_083_1 <;> assumption
