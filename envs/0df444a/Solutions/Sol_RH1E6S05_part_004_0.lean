-- Prove2me | solution 1 for RH1E6S05.part_004_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T12:15:43.83056+00:00
-- url     : https://prove2.me/submissions/3d067aa7-9647-4d23-9de6-1fa1847bd1ba

import Definitions.Def_RH1E6S05_D004_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0032 : RS5.BandZeros ((23090682371 : ℝ) / 65536) ((23095474362 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0032.s0 RH1E6S05_0032.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0032.s0 RH1E6S05_0032.rest = RH1E6S05_0032.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0032.s0 :: RH1E6S05_0032.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0032.s0.t = ((23090682371 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0032.s0]
  have e1 : RH1E6S05_0032.sL.t = ((23095474362 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0032.sL]
  rw [e0, e1] at h
  exact h

theorem band_0033 : RS5.BandZeros ((23095474362 : ℝ) / 65536) ((23100266262 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0033.s0 RH1E6S05_0033.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0033.s0 RH1E6S05_0033.rest = RH1E6S05_0033.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0033.s0 :: RH1E6S05_0033.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0033.s0.t = ((23095474362 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0033.s0]
  have e1 : RH1E6S05_0033.sL.t = ((23100266262 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0033.sL]
  rw [e0, e1] at h
  exact h

theorem part_004_0 : RS5.BandZeros ((23090682371 : ℝ) / 65536) ((23100266262 : ℝ) / 65536) 254 := by
  have g0 := band_0032
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0033
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((23090682371 : ℝ) / 65536) ((23100266262 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_004_0 <;> assumption
