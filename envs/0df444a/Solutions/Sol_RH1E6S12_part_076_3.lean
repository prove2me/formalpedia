-- Prove2me | solution 1 for RH1E6S12.part_076_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T17:01:40.197831+00:00
-- url     : https://prove2.me/submissions/7c1c5936-6c40-422b-931a-54175376fea6

import Definitions.Def_RH1E6S12_D076_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0614 : RS5.BandZeros ((48631288674 : ℝ) / 65536) ((48635760923 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0614.s0 RH1E6S12_0614.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0614.s0 RH1E6S12_0614.rest = RH1E6S12_0614.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0614.s0 :: RH1E6S12_0614.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0614.s0.t = ((48631288674 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0614.s0]
  have e1 : RH1E6S12_0614.sL.t = ((48635760923 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0614.sL]
  rw [e0, e1] at h
  exact h

theorem band_0615 : RS5.BandZeros ((48635760923 : ℝ) / 65536) ((48640235553 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0615.s0 RH1E6S12_0615.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0615.s0 RH1E6S12_0615.rest = RH1E6S12_0615.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0615.s0 :: RH1E6S12_0615.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0615.s0.t = ((48635760923 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0615.s0]
  have e1 : RH1E6S12_0615.sL.t = ((48640235553 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0615.sL]
  rw [e0, e1] at h
  exact h

theorem part_076_3 : RS5.BandZeros ((48631288674 : ℝ) / 65536) ((48640235553 : ℝ) / 65536) 254 := by
  have g0 := band_0614
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0615
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((48631288674 : ℝ) / 65536) ((48640235553 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_076_3 <;> assumption
