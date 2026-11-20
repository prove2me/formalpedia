-- Prove2me | solution 1 for RH1E6S00.part_023_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T21:33:15.518486+00:00
-- url     : https://prove2.me/submissions/1ec512a0-8d06-423e-9361-2f43aac44402

import Definitions.Def_RH1E6S00_D023_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0184 : RS5.BandZeros ((7540824904 : ℝ) / 65536) ((7546173599 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0184.s0 RH1E6S00_0184.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0184.s0 RH1E6S00_0184.rest = RH1E6S00_0184.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0184.s0 :: RH1E6S00_0184.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0184.s0.t = ((7540824904 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0184.s0]
  have e1 : RH1E6S00_0184.sL.t = ((7546173599 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0184.sL]
  rw [e0, e1] at h
  exact h

theorem band_0185 : RS5.BandZeros ((7546173599 : ℝ) / 65536) ((7551500935 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0185.s0 RH1E6S00_0185.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0185.s0 RH1E6S00_0185.rest = RH1E6S00_0185.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0185.s0 :: RH1E6S00_0185.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0185.s0.t = ((7546173599 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0185.s0]
  have e1 : RH1E6S00_0185.sL.t = ((7551500935 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0185.sL]
  rw [e0, e1] at h
  exact h

theorem part_023_0 : RS5.BandZeros ((7540824904 : ℝ) / 65536) ((7551500935 : ℝ) / 65536) 254 := by
  have g0 := band_0184
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0185
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((7540824904 : ℝ) / 65536) ((7551500935 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_023_0 <;> assumption
