-- Prove2me | solution 1 for RH1E6S12.part_083_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T17:21:57.247432+00:00
-- url     : https://prove2.me/submissions/113f03e2-d3da-4b44-b65e-9e5bc39c06e1

import Definitions.Def_RH1E6S12_D083_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0670 : RS5.BandZeros ((48881966955 : ℝ) / 65536) ((48886452238 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0670.s0 RH1E6S12_0670.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0670.s0 RH1E6S12_0670.rest = RH1E6S12_0670.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0670.s0 :: RH1E6S12_0670.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0670.s0.t = ((48881966955 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0670.s0]
  have e1 : RH1E6S12_0670.sL.t = ((48886452238 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0670.sL]
  rw [e0, e1] at h
  exact h

theorem band_0671 : RS5.BandZeros ((48886452238 : ℝ) / 65536) ((48890927869 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0671.s0 RH1E6S12_0671.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0671.s0 RH1E6S12_0671.rest = RH1E6S12_0671.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0671.s0 :: RH1E6S12_0671.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0671.s0.t = ((48886452238 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0671.s0]
  have e1 : RH1E6S12_0671.sL.t = ((48890927869 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0671.sL]
  rw [e0, e1] at h
  exact h

theorem part_083_3 : RS5.BandZeros ((48881966955 : ℝ) / 65536) ((48890927869 : ℝ) / 65536) 254 := by
  have g0 := band_0670
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0671
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((48881966955 : ℝ) / 65536) ((48890927869 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_083_3 <;> assumption
