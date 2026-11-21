-- Prove2me | solution 1 for RH1E6S05.part_077_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T16:20:43.199891+00:00
-- url     : https://prove2.me/submissions/d1621b97-b6dd-4be9-a4b8-d63e8cc1b561

import Definitions.Def_RH1E6S05_D077_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0622 : RS5.BandZeros ((25897443679 : ℝ) / 65536) ((25902157974 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0622.s0 RH1E6S05_0622.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0622.s0 RH1E6S05_0622.rest = RH1E6S05_0622.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0622.s0 :: RH1E6S05_0622.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0622.s0.t = ((25897443679 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0622.s0]
  have e1 : RH1E6S05_0622.sL.t = ((25902157974 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0622.sL]
  rw [e0, e1] at h
  exact h

theorem band_0623 : RS5.BandZeros ((25902157974 : ℝ) / 65536) ((25906909458 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0623.s0 RH1E6S05_0623.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0623.s0 RH1E6S05_0623.rest = RH1E6S05_0623.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0623.s0 :: RH1E6S05_0623.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0623.s0.t = ((25902157974 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0623.s0]
  have e1 : RH1E6S05_0623.sL.t = ((25906909458 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0623.sL]
  rw [e0, e1] at h
  exact h

theorem part_077_3 : RS5.BandZeros ((25897443679 : ℝ) / 65536) ((25906909458 : ℝ) / 65536) 254 := by
  have g0 := band_0622
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0623
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((25897443679 : ℝ) / 65536) ((25906909458 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_077_3 <;> assumption
