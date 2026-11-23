-- Prove2me | solution 1 for RH1E6S15.part_035_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T09:56:57.049532+00:00
-- url     : https://prove2.me/submissions/50b4d2e4-76a3-4bc4-a73d-7785036cb9c3

import Definitions.Def_RH1E6S15_D035_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0284 : RS5.BandZeros ((56961406385 : ℝ) / 65536) ((56965828289 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0284.s0 RH1E6S15_0284.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0284.s0 RH1E6S15_0284.rest = RH1E6S15_0284.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0284.s0 :: RH1E6S15_0284.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0284.s0.t = ((56961406385 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0284.s0]
  have e1 : RH1E6S15_0284.sL.t = ((56965828289 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0284.sL]
  rw [e0, e1] at h
  exact h

theorem band_0285 : RS5.BandZeros ((56965828289 : ℝ) / 65536) ((56970243421 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0285.s0 RH1E6S15_0285.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0285.s0 RH1E6S15_0285.rest = RH1E6S15_0285.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0285.s0 :: RH1E6S15_0285.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0285.s0.t = ((56965828289 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0285.s0]
  have e1 : RH1E6S15_0285.sL.t = ((56970243421 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0285.sL]
  rw [e0, e1] at h
  exact h

theorem part_035_2 : RS5.BandZeros ((56961406385 : ℝ) / 65536) ((56970243421 : ℝ) / 65536) 254 := by
  have g0 := band_0284
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0285
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((56961406385 : ℝ) / 65536) ((56970243421 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_035_2 <;> assumption
