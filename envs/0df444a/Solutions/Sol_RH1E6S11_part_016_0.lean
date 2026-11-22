-- Prove2me | solution 1 for RH1E6S11.part_016_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T03:45:58.272666+00:00
-- url     : https://prove2.me/submissions/7db5671e-cecb-4313-be41-a6f404e160c3

import Definitions.Def_RH1E6S11_D016_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0128 : RS5.BandZeros ((43177748282 : ℝ) / 65536) ((43182298660 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0128.s0 RH1E6S11_0128.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0128.s0 RH1E6S11_0128.rest = RH1E6S11_0128.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0128.s0 :: RH1E6S11_0128.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0128.s0.t = ((43177748282 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0128.s0]
  have e1 : RH1E6S11_0128.sL.t = ((43182298660 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0128.sL]
  rw [e0, e1] at h
  exact h

theorem band_0129 : RS5.BandZeros ((43182298660 : ℝ) / 65536) ((43186822281 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0129.s0 RH1E6S11_0129.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0129.s0 RH1E6S11_0129.rest = RH1E6S11_0129.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0129.s0 :: RH1E6S11_0129.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0129.s0.t = ((43182298660 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0129.s0]
  have e1 : RH1E6S11_0129.sL.t = ((43186822281 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0129.sL]
  rw [e0, e1] at h
  exact h

theorem part_016_0 : RS5.BandZeros ((43177748282 : ℝ) / 65536) ((43186822281 : ℝ) / 65536) 254 := by
  have g0 := band_0128
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0129
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((43177748282 : ℝ) / 65536) ((43186822281 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_016_0 <;> assumption
