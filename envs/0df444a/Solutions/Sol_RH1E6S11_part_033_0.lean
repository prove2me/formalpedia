-- Prove2me | solution 1 for RH1E6S11.part_033_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T04:33:55.116605+00:00
-- url     : https://prove2.me/submissions/c907f5c6-9e5a-465e-b1cd-f52d154c37e6

import Definitions.Def_RH1E6S11_D033_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0264 : RS5.BandZeros ((43792610108 : ℝ) / 65536) ((43797119351 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0264.s0 RH1E6S11_0264.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0264.s0 RH1E6S11_0264.rest = RH1E6S11_0264.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0264.s0 :: RH1E6S11_0264.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0264.s0.t = ((43792610108 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0264.s0]
  have e1 : RH1E6S11_0264.sL.t = ((43797119351 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0264.sL]
  rw [e0, e1] at h
  exact h

theorem band_0265 : RS5.BandZeros ((43797119351 : ℝ) / 65536) ((43801646341 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0265.s0 RH1E6S11_0265.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0265.s0 RH1E6S11_0265.rest = RH1E6S11_0265.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0265.s0 :: RH1E6S11_0265.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0265.s0.t = ((43797119351 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0265.s0]
  have e1 : RH1E6S11_0265.sL.t = ((43801646341 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0265.sL]
  rw [e0, e1] at h
  exact h

theorem part_033_0 : RS5.BandZeros ((43792610108 : ℝ) / 65536) ((43801646341 : ℝ) / 65536) 254 := by
  have g0 := band_0264
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0265
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((43792610108 : ℝ) / 65536) ((43801646341 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_033_0 <;> assumption
