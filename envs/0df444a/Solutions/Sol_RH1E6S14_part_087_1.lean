-- Prove2me | solution 1 for RH1E6S14.part_087_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T07:25:44.635717+00:00
-- url     : https://prove2.me/submissions/062d1b5b-cba2-4efa-a196-3511556a01ed

import Definitions.Def_RH1E6S14_D087_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0698 : RS5.BandZeros ((55526543060 : ℝ) / 65536) ((55530982896 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0698.s0 RH1E6S14_0698.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0698.s0 RH1E6S14_0698.rest = RH1E6S14_0698.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0698.s0 :: RH1E6S14_0698.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0698.s0.t = ((55526543060 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0698.s0]
  have e1 : RH1E6S14_0698.sL.t = ((55530982896 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0698.sL]
  rw [e0, e1] at h
  exact h

theorem band_0699 : RS5.BandZeros ((55530982896 : ℝ) / 65536) ((55535395431 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0699.s0 RH1E6S14_0699.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0699.s0 RH1E6S14_0699.rest = RH1E6S14_0699.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0699.s0 :: RH1E6S14_0699.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0699.s0.t = ((55530982896 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0699.s0]
  have e1 : RH1E6S14_0699.sL.t = ((55535395431 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0699.sL]
  rw [e0, e1] at h
  exact h

theorem part_087_1 : RS5.BandZeros ((55526543060 : ℝ) / 65536) ((55535395431 : ℝ) / 65536) 254 := by
  have g0 := band_0698
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0699
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((55526543060 : ℝ) / 65536) ((55535395431 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_087_1 <;> assumption
