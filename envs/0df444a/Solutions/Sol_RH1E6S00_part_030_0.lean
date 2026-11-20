-- Prove2me | solution 1 for RH1E6S00.part_030_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T21:47:10.16329+00:00
-- url     : https://prove2.me/submissions/16f92d37-b21d-4a9e-b3ca-f26c03ee1d5b

import Definitions.Def_RH1E6S00_D030_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0240 : RS5.BandZeros ((7838607177 : ℝ) / 65536) ((7843913967 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0240.s0 RH1E6S00_0240.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0240.s0 RH1E6S00_0240.rest = RH1E6S00_0240.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0240.s0 :: RH1E6S00_0240.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0240.s0.t = ((7838607177 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0240.s0]
  have e1 : RH1E6S00_0240.sL.t = ((7843913967 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0240.sL]
  rw [e0, e1] at h
  exact h

theorem band_0241 : RS5.BandZeros ((7843913967 : ℝ) / 65536) ((7849209946 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0241.s0 RH1E6S00_0241.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0241.s0 RH1E6S00_0241.rest = RH1E6S00_0241.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0241.s0 :: RH1E6S00_0241.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0241.s0.t = ((7843913967 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0241.s0]
  have e1 : RH1E6S00_0241.sL.t = ((7849209946 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0241.sL]
  rw [e0, e1] at h
  exact h

theorem part_030_0 : RS5.BandZeros ((7838607177 : ℝ) / 65536) ((7849209946 : ℝ) / 65536) 254 := by
  have g0 := band_0240
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0241
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((7838607177 : ℝ) / 65536) ((7849209946 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_030_0 <;> assumption
