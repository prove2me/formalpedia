-- Prove2me | solution 1 for RH1E6S14.part_087_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T07:25:42.719639+00:00
-- url     : https://prove2.me/submissions/c9a26edc-45fd-4a88-9345-b01799c561b2

import Definitions.Def_RH1E6S14_D087_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0696 : RS5.BandZeros ((55517680653 : ℝ) / 65536) ((55522117272 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0696.s0 RH1E6S14_0696.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0696.s0 RH1E6S14_0696.rest = RH1E6S14_0696.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0696.s0 :: RH1E6S14_0696.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0696.s0.t = ((55517680653 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0696.s0]
  have e1 : RH1E6S14_0696.sL.t = ((55522117272 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0696.sL]
  rw [e0, e1] at h
  exact h

theorem band_0697 : RS5.BandZeros ((55522117272 : ℝ) / 65536) ((55526543060 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0697.s0 RH1E6S14_0697.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0697.s0 RH1E6S14_0697.rest = RH1E6S14_0697.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0697.s0 :: RH1E6S14_0697.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0697.s0.t = ((55522117272 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0697.s0]
  have e1 : RH1E6S14_0697.sL.t = ((55526543060 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0697.sL]
  rw [e0, e1] at h
  exact h

theorem part_087_0 : RS5.BandZeros ((55517680653 : ℝ) / 65536) ((55526543060 : ℝ) / 65536) 254 := by
  have g0 := band_0696
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0697
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((55517680653 : ℝ) / 65536) ((55526543060 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_087_0 <;> assumption
