-- Prove2me | solution 1 for RH1E6S04.part_061_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T10:42:57.539822+00:00
-- url     : https://prove2.me/submissions/952a4455-cc38-476a-8bc5-03419dd14a92

import Definitions.Def_RH1E6S04_D061_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0490 : RS5.BandZeros ((22026549570 : ℝ) / 65536) ((22031352870 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0490.s0 RH1E6S04_0490.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0490.s0 RH1E6S04_0490.rest = RH1E6S04_0490.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0490.s0 :: RH1E6S04_0490.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0490.s0.t = ((22026549570 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0490.s0]
  have e1 : RH1E6S04_0490.sL.t = ((22031352870 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0490.sL]
  rw [e0, e1] at h
  exact h

theorem band_0491 : RS5.BandZeros ((22031352870 : ℝ) / 65536) ((22036165528 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0491.s0 RH1E6S04_0491.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0491.s0 RH1E6S04_0491.rest = RH1E6S04_0491.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0491.s0 :: RH1E6S04_0491.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0491.s0.t = ((22031352870 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0491.s0]
  have e1 : RH1E6S04_0491.sL.t = ((22036165528 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0491.sL]
  rw [e0, e1] at h
  exact h

theorem part_061_1 : RS5.BandZeros ((22026549570 : ℝ) / 65536) ((22036165528 : ℝ) / 65536) 254 := by
  have g0 := band_0490
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0491
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((22026549570 : ℝ) / 65536) ((22036165528 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_061_1 <;> assumption
