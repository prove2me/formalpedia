-- Prove2me | solution 1 for RH1E6S02.part_031_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T03:12:58.408177+00:00
-- url     : https://prove2.me/submissions/acfd80a0-3d55-4c85-81ff-7c1dfd3c58db

import Definitions.Def_RH1E6S02_D031_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0248 : RS5.BandZeros ((14352537445 : ℝ) / 65536) ((14357543932 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0248.s0 RH1E6S02_0248.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0248.s0 RH1E6S02_0248.rest = RH1E6S02_0248.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0248.s0 :: RH1E6S02_0248.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0248.s0.t = ((14352537445 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0248.s0]
  have e1 : RH1E6S02_0248.sL.t = ((14357543932 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0248.sL]
  rw [e0, e1] at h
  exact h

theorem band_0249 : RS5.BandZeros ((14357543932 : ℝ) / 65536) ((14362540463 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0249.s0 RH1E6S02_0249.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0249.s0 RH1E6S02_0249.rest = RH1E6S02_0249.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0249.s0 :: RH1E6S02_0249.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0249.s0.t = ((14357543932 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0249.s0]
  have e1 : RH1E6S02_0249.sL.t = ((14362540463 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0249.sL]
  rw [e0, e1] at h
  exact h

theorem part_031_0 : RS5.BandZeros ((14352537445 : ℝ) / 65536) ((14362540463 : ℝ) / 65536) 254 := by
  have g0 := band_0248
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0249
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((14352537445 : ℝ) / 65536) ((14362540463 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_031_0 <;> assumption
