-- Prove2me | solution 1 for RH1E6S14.part_028_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T04:08:05.727666+00:00
-- url     : https://prove2.me/submissions/2f8e15fe-72aa-4e6e-b481-9ac77b3816aa

import Definitions.Def_RH1E6S14_D028_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0228 : RS5.BandZeros ((53442330332 : ℝ) / 65536) ((53446764967 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0228.s0 RH1E6S14_0228.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0228.s0 RH1E6S14_0228.rest = RH1E6S14_0228.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0228.s0 :: RH1E6S14_0228.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0228.s0.t = ((53442330332 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0228.s0]
  have e1 : RH1E6S14_0228.sL.t = ((53446764967 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0228.sL]
  rw [e0, e1] at h
  exact h

theorem band_0229 : RS5.BandZeros ((53446764967 : ℝ) / 65536) ((53451228591 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0229.s0 RH1E6S14_0229.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0229.s0 RH1E6S14_0229.rest = RH1E6S14_0229.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0229.s0 :: RH1E6S14_0229.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0229.s0.t = ((53446764967 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0229.s0]
  have e1 : RH1E6S14_0229.sL.t = ((53451228591 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0229.sL]
  rw [e0, e1] at h
  exact h

theorem part_028_2 : RS5.BandZeros ((53442330332 : ℝ) / 65536) ((53451228591 : ℝ) / 65536) 254 := by
  have g0 := band_0228
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0229
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((53442330332 : ℝ) / 65536) ((53451228591 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_028_2 <;> assumption
