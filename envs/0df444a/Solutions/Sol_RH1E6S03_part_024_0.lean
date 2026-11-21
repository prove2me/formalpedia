-- Prove2me | solution 1 for RH1E6S03.part_024_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T06:08:10.606466+00:00
-- url     : https://prove2.me/submissions/460bad93-c671-4ed9-9e93-719f4f29ca74

import Definitions.Def_RH1E6S03_D024_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0192 : RS5.BandZeros ((17329479319 : ℝ) / 65536) ((17334410136 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0192.s0 RH1E6S03_0192.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0192.s0 RH1E6S03_0192.rest = RH1E6S03_0192.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0192.s0 :: RH1E6S03_0192.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0192.s0.t = ((17329479319 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0192.s0]
  have e1 : RH1E6S03_0192.sL.t = ((17334410136 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0192.sL]
  rw [e0, e1] at h
  exact h

theorem band_0193 : RS5.BandZeros ((17334410136 : ℝ) / 65536) ((17339302149 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0193.s0 RH1E6S03_0193.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0193.s0 RH1E6S03_0193.rest = RH1E6S03_0193.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0193.s0 :: RH1E6S03_0193.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0193.s0.t = ((17334410136 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0193.s0]
  have e1 : RH1E6S03_0193.sL.t = ((17339302149 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0193.sL]
  rw [e0, e1] at h
  exact h

theorem part_024_0 : RS5.BandZeros ((17329479319 : ℝ) / 65536) ((17339302149 : ℝ) / 65536) 254 := by
  have g0 := band_0192
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0193
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((17329479319 : ℝ) / 65536) ((17339302149 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_024_0 <;> assumption
