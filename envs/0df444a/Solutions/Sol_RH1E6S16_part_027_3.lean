-- Prove2me | solution 1 for RH1E6S16.part_027_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T15:36:00.267439+00:00
-- url     : https://prove2.me/submissions/1b80d326-5350-47bb-8e29-b21e5716d409

import Definitions.Def_RH1E6S16_D027_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0222 : RS5.BandZeros ((59959570854 : ℝ) / 65536) ((59963987343 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0222.s0 RH1E6S16_0222.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0222.s0 RH1E6S16_0222.rest = RH1E6S16_0222.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0222.s0 :: RH1E6S16_0222.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0222.s0.t = ((59959570854 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0222.s0]
  have e1 : RH1E6S16_0222.sL.t = ((59963987343 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0222.sL]
  rw [e0, e1] at h
  exact h

theorem band_0223 : RS5.BandZeros ((59963987343 : ℝ) / 65536) ((59968378265 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0223.s0 RH1E6S16_0223.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0223.s0 RH1E6S16_0223.rest = RH1E6S16_0223.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0223.s0 :: RH1E6S16_0223.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0223.s0.t = ((59963987343 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0223.s0]
  have e1 : RH1E6S16_0223.sL.t = ((59968378265 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0223.sL]
  rw [e0, e1] at h
  exact h

theorem part_027_3 : RS5.BandZeros ((59959570854 : ℝ) / 65536) ((59968378265 : ℝ) / 65536) 254 := by
  have g0 := band_0222
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0223
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((59959570854 : ℝ) / 65536) ((59968378265 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_027_3 <;> assumption
