-- Prove2me | solution 1 for RH1E6S12.part_074_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T16:53:08.432418+00:00
-- url     : https://prove2.me/submissions/4f5cd60f-a418-4f27-903e-792c3e6bf82d

import Definitions.Def_RH1E6S12_D074_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0592 : RS5.BandZeros ((48532778373 : ℝ) / 65536) ((48537242760 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0592.s0 RH1E6S12_0592.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0592.s0 RH1E6S12_0592.rest = RH1E6S12_0592.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0592.s0 :: RH1E6S12_0592.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0592.s0.t = ((48532778373 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0592.s0]
  have e1 : RH1E6S12_0592.sL.t = ((48537242760 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0592.sL]
  rw [e0, e1] at h
  exact h

theorem band_0593 : RS5.BandZeros ((48537242760 : ℝ) / 65536) ((48541738677 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0593.s0 RH1E6S12_0593.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0593.s0 RH1E6S12_0593.rest = RH1E6S12_0593.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0593.s0 :: RH1E6S12_0593.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0593.s0.t = ((48537242760 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0593.s0]
  have e1 : RH1E6S12_0593.sL.t = ((48541738677 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0593.sL]
  rw [e0, e1] at h
  exact h

theorem part_074_0 : RS5.BandZeros ((48532778373 : ℝ) / 65536) ((48541738677 : ℝ) / 65536) 254 := by
  have g0 := band_0592
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0593
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((48532778373 : ℝ) / 65536) ((48541738677 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_074_0 <;> assumption
