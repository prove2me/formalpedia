-- Prove2me | solution 1 for RH1E6S10.part_010_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T17:55:50.260425+00:00
-- url     : https://prove2.me/submissions/32485b06-1b30-4c59-9b2b-79bdad8022c8

import Definitions.Def_RH1E6S10_D010_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0080 : RS5.BandZeros ((39686321604 : ℝ) / 65536) ((39690878502 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0080.s0 RH1E6S10_0080.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0080.s0 RH1E6S10_0080.rest = RH1E6S10_0080.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0080.s0 :: RH1E6S10_0080.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0080.s0.t = ((39686321604 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0080.s0]
  have e1 : RH1E6S10_0080.sL.t = ((39690878502 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0080.sL]
  rw [e0, e1] at h
  exact h

theorem band_0081 : RS5.BandZeros ((39690878502 : ℝ) / 65536) ((39695453294 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0081.s0 RH1E6S10_0081.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0081.s0 RH1E6S10_0081.rest = RH1E6S10_0081.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0081.s0 :: RH1E6S10_0081.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0081.s0.t = ((39690878502 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0081.s0]
  have e1 : RH1E6S10_0081.sL.t = ((39695453294 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0081.sL]
  rw [e0, e1] at h
  exact h

theorem part_010_0 : RS5.BandZeros ((39686321604 : ℝ) / 65536) ((39695453294 : ℝ) / 65536) 254 := by
  have g0 := band_0080
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0081
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((39686321604 : ℝ) / 65536) ((39695453294 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_010_0 <;> assumption
