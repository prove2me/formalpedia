-- Prove2me | solution 1 for RH1E6S12.part_067_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T16:33:05.397+00:00
-- url     : https://prove2.me/submissions/2c92ff74-81d1-427b-98d8-803dd338391a

import Definitions.Def_RH1E6S12_D067_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0540 : RS5.BandZeros ((48299833033 : ℝ) / 65536) ((48304337138 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0540.s0 RH1E6S12_0540.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0540.s0 RH1E6S12_0540.rest = RH1E6S12_0540.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0540.s0 :: RH1E6S12_0540.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0540.s0.t = ((48299833033 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0540.s0]
  have e1 : RH1E6S12_0540.sL.t = ((48304337138 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0540.sL]
  rw [e0, e1] at h
  exact h

theorem band_0541 : RS5.BandZeros ((48304337138 : ℝ) / 65536) ((48308812027 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0541.s0 RH1E6S12_0541.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0541.s0 RH1E6S12_0541.rest = RH1E6S12_0541.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0541.s0 :: RH1E6S12_0541.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0541.s0.t = ((48304337138 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0541.s0]
  have e1 : RH1E6S12_0541.sL.t = ((48308812027 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0541.sL]
  rw [e0, e1] at h
  exact h

theorem part_067_2 : RS5.BandZeros ((48299833033 : ℝ) / 65536) ((48308812027 : ℝ) / 65536) 254 := by
  have g0 := band_0540
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0541
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((48299833033 : ℝ) / 65536) ((48308812027 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_067_2 <;> assumption
