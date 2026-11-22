-- Prove2me | solution 1 for RH1E6S10.part_070_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T02:07:23.857308+00:00
-- url     : https://prove2.me/submissions/2ff4a6b8-4042-465d-8df2-2a980991d2ee

import Definitions.Def_RH1E6S10_D070_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0560 : RS5.BandZeros ((41868499943 : ℝ) / 65536) ((41873044615 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0560.s0 RH1E6S10_0560.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0560.s0 RH1E6S10_0560.rest = RH1E6S10_0560.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0560.s0 :: RH1E6S10_0560.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0560.s0.t = ((41868499943 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0560.s0]
  have e1 : RH1E6S10_0560.sL.t = ((41873044615 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0560.sL]
  rw [e0, e1] at h
  exact h

theorem band_0561 : RS5.BandZeros ((41873044615 : ℝ) / 65536) ((41877598172 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0561.s0 RH1E6S10_0561.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0561.s0 RH1E6S10_0561.rest = RH1E6S10_0561.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0561.s0 :: RH1E6S10_0561.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0561.s0.t = ((41873044615 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0561.s0]
  have e1 : RH1E6S10_0561.sL.t = ((41877598172 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0561.sL]
  rw [e0, e1] at h
  exact h

theorem part_070_0 : RS5.BandZeros ((41868499943 : ℝ) / 65536) ((41877598172 : ℝ) / 65536) 254 := by
  have g0 := band_0560
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0561
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((41868499943 : ℝ) / 65536) ((41877598172 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_070_0 <;> assumption
