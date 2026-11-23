-- Prove2me | solution 1 for RH1E6S15.part_081_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T12:57:31.141605+00:00
-- url     : https://prove2.me/submissions/fe5ac4c8-ed2b-442a-8cad-345a162b14e6

import Definitions.Def_RH1E6S15_D081_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0648 : RS5.BandZeros ((58567571574 : ℝ) / 65536) ((58571999643 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0648.s0 RH1E6S15_0648.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0648.s0 RH1E6S15_0648.rest = RH1E6S15_0648.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0648.s0 :: RH1E6S15_0648.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0648.s0.t = ((58567571574 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0648.s0]
  have e1 : RH1E6S15_0648.sL.t = ((58571999643 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0648.sL]
  rw [e0, e1] at h
  exact h

theorem band_0649 : RS5.BandZeros ((58571999643 : ℝ) / 65536) ((58576401345 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0649.s0 RH1E6S15_0649.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0649.s0 RH1E6S15_0649.rest = RH1E6S15_0649.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0649.s0 :: RH1E6S15_0649.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0649.s0.t = ((58571999643 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0649.s0]
  have e1 : RH1E6S15_0649.sL.t = ((58576401345 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0649.sL]
  rw [e0, e1] at h
  exact h

theorem part_081_0 : RS5.BandZeros ((58567571574 : ℝ) / 65536) ((58576401345 : ℝ) / 65536) 254 := by
  have g0 := band_0648
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0649
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((58567571574 : ℝ) / 65536) ((58576401345 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_081_0 <;> assumption
