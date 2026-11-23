-- Prove2me | solution 1 for RH1E6S13.part_086_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T02:04:47.564203+00:00
-- url     : https://prove2.me/submissions/624a63c9-b99b-4c5d-bf04-9739a8a9081b

import Definitions.Def_RH1E6S13_D086_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0690 : RS5.BandZeros ((52230655267 : ℝ) / 65536) ((52235114418 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0690.s0 RH1E6S13_0690.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0690.s0 RH1E6S13_0690.rest = RH1E6S13_0690.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0690.s0 :: RH1E6S13_0690.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0690.s0.t = ((52230655267 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0690.s0]
  have e1 : RH1E6S13_0690.sL.t = ((52235114418 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0690.sL]
  rw [e0, e1] at h
  exact h

theorem band_0691 : RS5.BandZeros ((52235114418 : ℝ) / 65536) ((52239556015 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0691.s0 RH1E6S13_0691.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0691.s0 RH1E6S13_0691.rest = RH1E6S13_0691.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0691.s0 :: RH1E6S13_0691.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0691.s0.t = ((52235114418 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0691.s0]
  have e1 : RH1E6S13_0691.sL.t = ((52239556015 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0691.sL]
  rw [e0, e1] at h
  exact h

theorem part_086_1 : RS5.BandZeros ((52230655267 : ℝ) / 65536) ((52239556015 : ℝ) / 65536) 254 := by
  have g0 := band_0690
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0691
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((52230655267 : ℝ) / 65536) ((52239556015 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_086_1 <;> assumption
