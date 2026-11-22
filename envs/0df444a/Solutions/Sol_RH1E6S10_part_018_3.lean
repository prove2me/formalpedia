-- Prove2me | solution 1 for RH1E6S10.part_018_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T18:53:33.85022+00:00
-- url     : https://prove2.me/submissions/f3a31347-1deb-424b-99fc-143c87c4c2d5

import Definitions.Def_RH1E6S10_D018_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0150 : RS5.BandZeros ((40005194707 : ℝ) / 65536) ((40009739465 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0150.s0 RH1E6S10_0150.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0150.s0 RH1E6S10_0150.rest = RH1E6S10_0150.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0150.s0 :: RH1E6S10_0150.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0150.s0.t = ((40005194707 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0150.s0]
  have e1 : RH1E6S10_0150.sL.t = ((40009739465 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0150.sL]
  rw [e0, e1] at h
  exact h

theorem band_0151 : RS5.BandZeros ((40009739465 : ℝ) / 65536) ((40014293142 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0151.s0 RH1E6S10_0151.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0151.s0 RH1E6S10_0151.rest = RH1E6S10_0151.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0151.s0 :: RH1E6S10_0151.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0151.s0.t = ((40009739465 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0151.s0]
  have e1 : RH1E6S10_0151.sL.t = ((40014293142 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0151.sL]
  rw [e0, e1] at h
  exact h

theorem part_018_3 : RS5.BandZeros ((40005194707 : ℝ) / 65536) ((40014293142 : ℝ) / 65536) 254 := by
  have g0 := band_0150
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0151
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((40005194707 : ℝ) / 65536) ((40014293142 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_018_3 <;> assumption
