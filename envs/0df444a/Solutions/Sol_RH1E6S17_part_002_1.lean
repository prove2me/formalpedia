-- Prove2me | solution 1 for RH1E6S17.part_002_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T19:50:05.670125+00:00
-- url     : https://prove2.me/submissions/d4eb3f06-08ec-48c4-b65d-6a9b04355003

import Definitions.Def_RH1E6S17_D002_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0018 : RS5.BandZeros ((62338119092 : ℝ) / 65536) ((62342529371 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0018.s0 RH1E6S17_0018.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0018.s0 RH1E6S17_0018.rest = RH1E6S17_0018.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0018.s0 :: RH1E6S17_0018.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0018.s0.t = ((62338119092 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0018.s0]
  have e1 : RH1E6S17_0018.sL.t = ((62342529371 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0018.sL]
  rw [e0, e1] at h
  exact h

theorem band_0019 : RS5.BandZeros ((62342529371 : ℝ) / 65536) ((62346896471 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0019.s0 RH1E6S17_0019.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0019.s0 RH1E6S17_0019.rest = RH1E6S17_0019.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0019.s0 :: RH1E6S17_0019.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0019.s0.t = ((62342529371 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0019.s0]
  have e1 : RH1E6S17_0019.sL.t = ((62346896471 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0019.sL]
  rw [e0, e1] at h
  exact h

theorem part_002_1 : RS5.BandZeros ((62338119092 : ℝ) / 65536) ((62346896471 : ℝ) / 65536) 254 := by
  have g0 := band_0018
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0019
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((62338119092 : ℝ) / 65536) ((62346896471 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_002_1 <;> assumption
