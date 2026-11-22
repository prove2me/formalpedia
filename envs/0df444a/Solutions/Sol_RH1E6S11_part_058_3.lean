-- Prove2me | solution 1 for RH1E6S11.part_058_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T05:47:30.76293+00:00
-- url     : https://prove2.me/submissions/3f19976d-debb-488a-b8b1-57c931189553

import Definitions.Def_RH1E6S11_D058_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0470 : RS5.BandZeros ((44722512336 : ℝ) / 65536) ((44727013408 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0470.s0 RH1E6S11_0470.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0470.s0 RH1E6S11_0470.rest = RH1E6S11_0470.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0470.s0 :: RH1E6S11_0470.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0470.s0.t = ((44722512336 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0470.s0]
  have e1 : RH1E6S11_0470.sL.t = ((44727013408 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0470.sL]
  rw [e0, e1] at h
  exact h

theorem band_0471 : RS5.BandZeros ((44727013408 : ℝ) / 65536) ((44731532197 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0471.s0 RH1E6S11_0471.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0471.s0 RH1E6S11_0471.rest = RH1E6S11_0471.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0471.s0 :: RH1E6S11_0471.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0471.s0.t = ((44727013408 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0471.s0]
  have e1 : RH1E6S11_0471.sL.t = ((44731532197 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0471.sL]
  rw [e0, e1] at h
  exact h

theorem part_058_3 : RS5.BandZeros ((44722512336 : ℝ) / 65536) ((44731532197 : ℝ) / 65536) 254 := by
  have g0 := band_0470
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0471
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((44722512336 : ℝ) / 65536) ((44731532197 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_058_3 <;> assumption
