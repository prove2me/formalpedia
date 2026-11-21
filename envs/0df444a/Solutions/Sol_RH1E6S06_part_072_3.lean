-- Prove2me | solution 1 for RH1E6S06.part_072_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T22:05:32.862686+00:00
-- url     : https://prove2.me/submissions/75d5d04b-12f4-494c-bbc8-703bd232efc6

import Definitions.Def_RH1E6S06_D072_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0582 : RS5.BandZeros ((28953454066 : ℝ) / 65536) ((28958145836 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0582.s0 RH1E6S06_0582.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0582.s0 RH1E6S06_0582.rest = RH1E6S06_0582.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0582.s0 :: RH1E6S06_0582.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0582.s0.t = ((28953454066 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0582.s0]
  have e1 : RH1E6S06_0582.sL.t = ((28958145836 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0582.sL]
  rw [e0, e1] at h
  exact h

theorem band_0583 : RS5.BandZeros ((28958145836 : ℝ) / 65536) ((28962814265 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0583.s0 RH1E6S06_0583.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0583.s0 RH1E6S06_0583.rest = RH1E6S06_0583.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0583.s0 :: RH1E6S06_0583.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0583.s0.t = ((28958145836 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0583.s0]
  have e1 : RH1E6S06_0583.sL.t = ((28962814265 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0583.sL]
  rw [e0, e1] at h
  exact h

theorem part_072_3 : RS5.BandZeros ((28953454066 : ℝ) / 65536) ((28962814265 : ℝ) / 65536) 254 := by
  have g0 := band_0582
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0583
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((28953454066 : ℝ) / 65536) ((28962814265 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_072_3 <;> assumption
