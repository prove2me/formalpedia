-- Prove2me | solution 1 for RH1E6S00.part_033_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T21:54:13.405052+00:00
-- url     : https://prove2.me/submissions/5efdbf2b-bbda-40ae-8758-08c8cb8b5d22

import Definitions.Def_RH1E6S00_D033_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0264 : RS5.BandZeros ((7965880653 : ℝ) / 65536) ((7971178786 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0264.s0 RH1E6S00_0264.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0264.s0 RH1E6S00_0264.rest = RH1E6S00_0264.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0264.s0 :: RH1E6S00_0264.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0264.s0.t = ((7965880653 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0264.s0]
  have e1 : RH1E6S00_0264.sL.t = ((7971178786 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0264.sL]
  rw [e0, e1] at h
  exact h

theorem band_0265 : RS5.BandZeros ((7971178786 : ℝ) / 65536) ((7976476563 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0265.s0 RH1E6S00_0265.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0265.s0 RH1E6S00_0265.rest = RH1E6S00_0265.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0265.s0 :: RH1E6S00_0265.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0265.s0.t = ((7971178786 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0265.s0]
  have e1 : RH1E6S00_0265.sL.t = ((7976476563 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0265.sL]
  rw [e0, e1] at h
  exact h

theorem part_033_0 : RS5.BandZeros ((7965880653 : ℝ) / 65536) ((7976476563 : ℝ) / 65536) 254 := by
  have g0 := band_0264
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0265
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((7965880653 : ℝ) / 65536) ((7976476563 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_033_0 <;> assumption
