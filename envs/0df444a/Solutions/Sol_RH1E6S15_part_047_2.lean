-- Prove2me | solution 1 for RH1E6S15.part_047_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T10:38:33.82895+00:00
-- url     : https://prove2.me/submissions/e81c5267-b19b-4682-8e4c-f73955479d5b

import Definitions.Def_RH1E6S15_D047_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0380 : RS5.BandZeros ((57385369834 : ℝ) / 65536) ((57389802244 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0380.s0 RH1E6S15_0380.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0380.s0 RH1E6S15_0380.rest = RH1E6S15_0380.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0380.s0 :: RH1E6S15_0380.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0380.s0.t = ((57385369834 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0380.s0]
  have e1 : RH1E6S15_0380.sL.t = ((57389802244 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0380.sL]
  rw [e0, e1] at h
  exact h

theorem band_0381 : RS5.BandZeros ((57389802244 : ℝ) / 65536) ((57394208553 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0381.s0 RH1E6S15_0381.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0381.s0 RH1E6S15_0381.rest = RH1E6S15_0381.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0381.s0 :: RH1E6S15_0381.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0381.s0.t = ((57389802244 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0381.s0]
  have e1 : RH1E6S15_0381.sL.t = ((57394208553 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0381.sL]
  rw [e0, e1] at h
  exact h

theorem part_047_2 : RS5.BandZeros ((57385369834 : ℝ) / 65536) ((57394208553 : ℝ) / 65536) 254 := by
  have g0 := band_0380
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0381
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((57385369834 : ℝ) / 65536) ((57394208553 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_047_2 <;> assumption
