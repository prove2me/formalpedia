-- Prove2me | solution 1 for RH1E6S10.part_084_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T02:44:09.091262+00:00
-- url     : https://prove2.me/submissions/ed863cc6-cc44-4b5b-947f-10eedd7c9789

import Definitions.Def_RH1E6S10_D084_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0672 : RS5.BandZeros ((42376248535 : ℝ) / 65536) ((42380779542 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0672.s0 RH1E6S10_0672.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0672.s0 RH1E6S10_0672.rest = RH1E6S10_0672.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0672.s0 :: RH1E6S10_0672.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0672.s0.t = ((42376248535 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0672.s0]
  have e1 : RH1E6S10_0672.sL.t = ((42380779542 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0672.sL]
  rw [e0, e1] at h
  exact h

theorem band_0673 : RS5.BandZeros ((42380779542 : ℝ) / 65536) ((42385296012 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0673.s0 RH1E6S10_0673.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0673.s0 RH1E6S10_0673.rest = RH1E6S10_0673.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0673.s0 :: RH1E6S10_0673.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0673.s0.t = ((42380779542 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0673.s0]
  have e1 : RH1E6S10_0673.sL.t = ((42385296012 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0673.sL]
  rw [e0, e1] at h
  exact h

theorem part_084_0 : RS5.BandZeros ((42376248535 : ℝ) / 65536) ((42385296012 : ℝ) / 65536) 254 := by
  have g0 := band_0672
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0673
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((42376248535 : ℝ) / 65536) ((42385296012 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_084_0 <;> assumption
