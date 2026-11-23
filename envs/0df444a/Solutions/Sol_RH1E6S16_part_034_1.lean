-- Prove2me | solution 1 for RH1E6S16.part_034_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T16:03:13.353129+00:00
-- url     : https://prove2.me/submissions/0443d8ca-51de-4d5f-9a4e-64beab9b0770

import Definitions.Def_RH1E6S16_D034_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0274 : RS5.BandZeros ((60188271490 : ℝ) / 65536) ((60192687510 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0274.s0 RH1E6S16_0274.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0274.s0 RH1E6S16_0274.rest = RH1E6S16_0274.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0274.s0 :: RH1E6S16_0274.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0274.s0.t = ((60188271490 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0274.s0]
  have e1 : RH1E6S16_0274.sL.t = ((60192687510 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0274.sL]
  rw [e0, e1] at h
  exact h

theorem band_0275 : RS5.BandZeros ((60192687510 : ℝ) / 65536) ((60197078992 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0275.s0 RH1E6S16_0275.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0275.s0 RH1E6S16_0275.rest = RH1E6S16_0275.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0275.s0 :: RH1E6S16_0275.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0275.s0.t = ((60192687510 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0275.s0]
  have e1 : RH1E6S16_0275.sL.t = ((60197078992 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0275.sL]
  rw [e0, e1] at h
  exact h

theorem part_034_1 : RS5.BandZeros ((60188271490 : ℝ) / 65536) ((60197078992 : ℝ) / 65536) 254 := by
  have g0 := band_0274
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0275
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((60188271490 : ℝ) / 65536) ((60197078992 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_034_1 <;> assumption
