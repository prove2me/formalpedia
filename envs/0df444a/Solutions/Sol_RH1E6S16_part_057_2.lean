-- Prove2me | solution 1 for RH1E6S16.part_057_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T17:34:20.051935+00:00
-- url     : https://prove2.me/submissions/e0469e30-46f9-464b-ae68-b5792e797130

import Definitions.Def_RH1E6S16_D057_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0460 : RS5.BandZeros ((61005716218 : ℝ) / 65536) ((61010121199 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0460.s0 RH1E6S16_0460.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0460.s0 RH1E6S16_0460.rest = RH1E6S16_0460.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0460.s0 :: RH1E6S16_0460.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0460.s0.t = ((61005716218 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0460.s0]
  have e1 : RH1E6S16_0460.sL.t = ((61010121199 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0460.sL]
  rw [e0, e1] at h
  exact h

theorem band_0461 : RS5.BandZeros ((61010121199 : ℝ) / 65536) ((61014505199 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0461.s0 RH1E6S16_0461.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0461.s0 RH1E6S16_0461.rest = RH1E6S16_0461.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0461.s0 :: RH1E6S16_0461.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0461.s0.t = ((61010121199 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0461.s0]
  have e1 : RH1E6S16_0461.sL.t = ((61014505199 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0461.sL]
  rw [e0, e1] at h
  exact h

theorem part_057_2 : RS5.BandZeros ((61005716218 : ℝ) / 65536) ((61014505199 : ℝ) / 65536) 254 := by
  have g0 := band_0460
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0461
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((61005716218 : ℝ) / 65536) ((61014505199 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_057_2 <;> assumption
