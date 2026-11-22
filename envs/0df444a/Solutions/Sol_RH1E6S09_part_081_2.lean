-- Prove2me | solution 1 for RH1E6S09.part_081_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T15:56:50.812518+00:00
-- url     : https://prove2.me/submissions/b8cc290d-684c-498c-b7dc-78945b6e1ee8

import Definitions.Def_RH1E6S09_D081_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0652 : RS5.BandZeros ((39030425982 : ℝ) / 65536) ((39035019530 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0652.s0 RH1E6S09_0652.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0652.s0 RH1E6S09_0652.rest = RH1E6S09_0652.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0652.s0 :: RH1E6S09_0652.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0652.s0.t = ((39030425982 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0652.s0]
  have e1 : RH1E6S09_0652.sL.t = ((39035019530 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0652.sL]
  rw [e0, e1] at h
  exact h

theorem band_0653 : RS5.BandZeros ((39035019530 : ℝ) / 65536) ((39039554038 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0653.s0 RH1E6S09_0653.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0653.s0 RH1E6S09_0653.rest = RH1E6S09_0653.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0653.s0 :: RH1E6S09_0653.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0653.s0.t = ((39035019530 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0653.s0]
  have e1 : RH1E6S09_0653.sL.t = ((39039554038 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0653.sL]
  rw [e0, e1] at h
  exact h

theorem part_081_2 : RS5.BandZeros ((39030425982 : ℝ) / 65536) ((39039554038 : ℝ) / 65536) 254 := by
  have g0 := band_0652
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0653
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((39030425982 : ℝ) / 65536) ((39039554038 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_081_2 <;> assumption
