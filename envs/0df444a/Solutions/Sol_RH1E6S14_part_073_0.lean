-- Prove2me | solution 1 for RH1E6S14.part_073_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T06:46:54.49187+00:00
-- url     : https://prove2.me/submissions/7a3260a8-f411-44c2-a98f-5343b5f323a3

import Definitions.Def_RH1E6S14_D073_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0584 : RS5.BandZeros ((55021631191 : ℝ) / 65536) ((55026067663 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0584.s0 RH1E6S14_0584.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0584.s0 RH1E6S14_0584.rest = RH1E6S14_0584.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0584.s0 :: RH1E6S14_0584.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0584.s0.t = ((55021631191 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0584.s0]
  have e1 : RH1E6S14_0584.sL.t = ((55026067663 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0584.sL]
  rw [e0, e1] at h
  exact h

theorem band_0585 : RS5.BandZeros ((55026067663 : ℝ) / 65536) ((55030475242 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0585.s0 RH1E6S14_0585.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0585.s0 RH1E6S14_0585.rest = RH1E6S14_0585.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0585.s0 :: RH1E6S14_0585.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0585.s0.t = ((55026067663 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0585.s0]
  have e1 : RH1E6S14_0585.sL.t = ((55030475242 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0585.sL]
  rw [e0, e1] at h
  exact h

theorem part_073_0 : RS5.BandZeros ((55021631191 : ℝ) / 65536) ((55030475242 : ℝ) / 65536) 254 := by
  have g0 := band_0584
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0585
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((55021631191 : ℝ) / 65536) ((55030475242 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_073_0 <;> assumption
