-- Prove2me | solution 1 for RH1E6S16.part_022_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T15:20:29.790795+00:00
-- url     : https://prove2.me/submissions/1df50edd-3d4a-4245-8ef5-dfa66172f8dc

import Definitions.Def_RH1E6S16_D022_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0180 : RS5.BandZeros ((59774798204 : ℝ) / 65536) ((59779225934 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0180.s0 RH1E6S16_0180.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0180.s0 RH1E6S16_0180.rest = RH1E6S16_0180.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0180.s0 :: RH1E6S16_0180.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0180.s0.t = ((59774798204 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0180.s0]
  have e1 : RH1E6S16_0180.sL.t = ((59779225934 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0180.sL]
  rw [e0, e1] at h
  exact h

theorem band_0181 : RS5.BandZeros ((59779225934 : ℝ) / 65536) ((59783612495 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0181.s0 RH1E6S16_0181.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0181.s0 RH1E6S16_0181.rest = RH1E6S16_0181.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0181.s0 :: RH1E6S16_0181.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0181.s0.t = ((59779225934 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0181.s0]
  have e1 : RH1E6S16_0181.sL.t = ((59783612495 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0181.sL]
  rw [e0, e1] at h
  exact h

theorem part_022_2 : RS5.BandZeros ((59774798204 : ℝ) / 65536) ((59783612495 : ℝ) / 65536) 254 := by
  have g0 := band_0180
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0181
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((59774798204 : ℝ) / 65536) ((59783612495 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_022_2 <;> assumption
