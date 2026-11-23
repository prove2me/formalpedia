-- Prove2me | solution 1 for RH1E6S16.part_058_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T17:40:22.718803+00:00
-- url     : https://prove2.me/submissions/ea850205-2a13-46aa-ad73-8a1e7daccd09

import Definitions.Def_RH1E6S16_D058_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0470 : RS5.BandZeros ((61049638328 : ℝ) / 65536) ((61054047698 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0470.s0 RH1E6S16_0470.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0470.s0 RH1E6S16_0470.rest = RH1E6S16_0470.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0470.s0 :: RH1E6S16_0470.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0470.s0.t = ((61049638328 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0470.s0]
  have e1 : RH1E6S16_0470.sL.t = ((61054047698 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0470.sL]
  rw [e0, e1] at h
  exact h

theorem band_0471 : RS5.BandZeros ((61054047698 : ℝ) / 65536) ((61058428788 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0471.s0 RH1E6S16_0471.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0471.s0 RH1E6S16_0471.rest = RH1E6S16_0471.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0471.s0 :: RH1E6S16_0471.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0471.s0.t = ((61054047698 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0471.s0]
  have e1 : RH1E6S16_0471.sL.t = ((61058428788 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0471.sL]
  rw [e0, e1] at h
  exact h

theorem part_058_3 : RS5.BandZeros ((61049638328 : ℝ) / 65536) ((61058428788 : ℝ) / 65536) 254 := by
  have g0 := band_0470
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0471
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((61049638328 : ℝ) / 65536) ((61058428788 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_058_3 <;> assumption
