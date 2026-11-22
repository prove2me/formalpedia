-- Prove2me | solution 1 for RH1E6S10.part_034_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T22:48:30.207677+00:00
-- url     : https://prove2.me/submissions/422cb299-3436-4c3b-9633-f0eaff12533b

import Definitions.Def_RH1E6S10_D034_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0274 : RS5.BandZeros ((40569523068 : ℝ) / 65536) ((40574071243 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0274.s0 RH1E6S10_0274.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0274.s0 RH1E6S10_0274.rest = RH1E6S10_0274.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0274.s0 :: RH1E6S10_0274.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0274.s0.t = ((40569523068 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0274.s0]
  have e1 : RH1E6S10_0274.sL.t = ((40574071243 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0274.sL]
  rw [e0, e1] at h
  exact h

theorem band_0275 : RS5.BandZeros ((40574071243 : ℝ) / 65536) ((40578610420 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0275.s0 RH1E6S10_0275.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0275.s0 RH1E6S10_0275.rest = RH1E6S10_0275.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0275.s0 :: RH1E6S10_0275.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0275.s0.t = ((40574071243 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0275.s0]
  have e1 : RH1E6S10_0275.sL.t = ((40578610420 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0275.sL]
  rw [e0, e1] at h
  exact h

theorem part_034_1 : RS5.BandZeros ((40569523068 : ℝ) / 65536) ((40578610420 : ℝ) / 65536) 254 := by
  have g0 := band_0274
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0275
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((40569523068 : ℝ) / 65536) ((40578610420 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_034_1 <;> assumption
