-- Prove2me | solution 1 for RH1E6S03.part_044_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T06:52:38.794938+00:00
-- url     : https://prove2.me/submissions/b87c0bd8-8576-4031-a890-de9575eafb82

import Definitions.Def_RH1E6S03_D044_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0358 : RS5.BandZeros ((18143020193 : ℝ) / 65536) ((18147910605 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0358.s0 RH1E6S03_0358.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0358.s0 RH1E6S03_0358.rest = RH1E6S03_0358.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0358.s0 :: RH1E6S03_0358.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0358.s0.t = ((18143020193 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0358.s0]
  have e1 : RH1E6S03_0358.sL.t = ((18147910605 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0358.sL]
  rw [e0, e1] at h
  exact h

theorem band_0359 : RS5.BandZeros ((18147910605 : ℝ) / 65536) ((18152800895 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0359.s0 RH1E6S03_0359.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0359.s0 RH1E6S03_0359.rest = RH1E6S03_0359.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0359.s0 :: RH1E6S03_0359.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0359.s0.t = ((18147910605 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0359.s0]
  have e1 : RH1E6S03_0359.sL.t = ((18152800895 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0359.sL]
  rw [e0, e1] at h
  exact h

theorem part_044_3 : RS5.BandZeros ((18143020193 : ℝ) / 65536) ((18152800895 : ℝ) / 65536) 254 := by
  have g0 := band_0358
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0359
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((18143020193 : ℝ) / 65536) ((18152800895 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_044_3 <;> assumption
