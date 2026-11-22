-- Prove2me | solution 1 for RH1E6S10.part_033_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T22:45:43.109111+00:00
-- url     : https://prove2.me/submissions/80943ada-d5fd-4438-9536-358dfd43e1e0

import Definitions.Def_RH1E6S10_D033_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0264 : RS5.BandZeros ((40524020969 : ℝ) / 65536) ((40528578542 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0264.s0 RH1E6S10_0264.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0264.s0 RH1E6S10_0264.rest = RH1E6S10_0264.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0264.s0 :: RH1E6S10_0264.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0264.s0.t = ((40524020969 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0264.s0]
  have e1 : RH1E6S10_0264.sL.t = ((40528578542 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0264.sL]
  rw [e0, e1] at h
  exact h

theorem band_0265 : RS5.BandZeros ((40528578542 : ℝ) / 65536) ((40533145024 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0265.s0 RH1E6S10_0265.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0265.s0 RH1E6S10_0265.rest = RH1E6S10_0265.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0265.s0 :: RH1E6S10_0265.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0265.s0.t = ((40528578542 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0265.s0]
  have e1 : RH1E6S10_0265.sL.t = ((40533145024 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0265.sL]
  rw [e0, e1] at h
  exact h

theorem part_033_0 : RS5.BandZeros ((40524020969 : ℝ) / 65536) ((40533145024 : ℝ) / 65536) 254 := by
  have g0 := band_0264
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0265
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((40524020969 : ℝ) / 65536) ((40533145024 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_033_0 <;> assumption
