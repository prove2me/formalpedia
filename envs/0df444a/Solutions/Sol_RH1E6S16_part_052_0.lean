-- Prove2me | solution 1 for RH1E6S16.part_052_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T17:25:06.152478+00:00
-- url     : https://prove2.me/submissions/26bdb4c7-4766-4cd4-b0a7-2bf1af6c8789

import Definitions.Def_RH1E6S16_D052_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0416 : RS5.BandZeros ((60812443542 : ℝ) / 65536) ((60816811521 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0416.s0 RH1E6S16_0416.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0416.s0 RH1E6S16_0416.rest = RH1E6S16_0416.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0416.s0 :: RH1E6S16_0416.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0416.s0.t = ((60812443542 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0416.s0]
  have e1 : RH1E6S16_0416.sL.t = ((60816811521 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0416.sL]
  rw [e0, e1] at h
  exact h

theorem band_0417 : RS5.BandZeros ((60816811521 : ℝ) / 65536) ((60821230633 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0417.s0 RH1E6S16_0417.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0417.s0 RH1E6S16_0417.rest = RH1E6S16_0417.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0417.s0 :: RH1E6S16_0417.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0417.s0.t = ((60816811521 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0417.s0]
  have e1 : RH1E6S16_0417.sL.t = ((60821230633 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0417.sL]
  rw [e0, e1] at h
  exact h

theorem part_052_0 : RS5.BandZeros ((60812443542 : ℝ) / 65536) ((60821230633 : ℝ) / 65536) 254 := by
  have g0 := band_0416
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0417
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((60812443542 : ℝ) / 65536) ((60821230633 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_052_0 <;> assumption
