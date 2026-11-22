-- Prove2me | solution 1 for RH1E6S13.part_042_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T23:01:41.765207+00:00
-- url     : https://prove2.me/submissions/b3c5fa71-08a0-4b52-8217-fab3076a6f3f

import Definitions.Def_RH1E6S13_D042_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0338 : RS5.BandZeros ((50662105063 : ℝ) / 65536) ((50666558247 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0338.s0 RH1E6S13_0338.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0338.s0 RH1E6S13_0338.rest = RH1E6S13_0338.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0338.s0 :: RH1E6S13_0338.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0338.s0.t = ((50662105063 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0338.s0]
  have e1 : RH1E6S13_0338.sL.t = ((50666558247 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0338.sL]
  rw [e0, e1] at h
  exact h

theorem band_0339 : RS5.BandZeros ((50666558247 : ℝ) / 65536) ((50671028964 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0339.s0 RH1E6S13_0339.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0339.s0 RH1E6S13_0339.rest = RH1E6S13_0339.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0339.s0 :: RH1E6S13_0339.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0339.s0.t = ((50666558247 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0339.s0]
  have e1 : RH1E6S13_0339.sL.t = ((50671028964 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0339.sL]
  rw [e0, e1] at h
  exact h

theorem part_042_1 : RS5.BandZeros ((50662105063 : ℝ) / 65536) ((50671028964 : ℝ) / 65536) 254 := by
  have g0 := band_0338
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0339
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((50662105063 : ℝ) / 65536) ((50671028964 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_042_1 <;> assumption
