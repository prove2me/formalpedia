-- Prove2me | solution 1 for RH1E6S04.part_074_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T11:10:44.330503+00:00
-- url     : https://prove2.me/submissions/7ada148e-b872-4c95-a1ce-2af3c8b41619

import Definitions.Def_RH1E6S04_D074_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0594 : RS5.BandZeros ((22525601255 : ℝ) / 65536) ((22530366384 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0594.s0 RH1E6S04_0594.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0594.s0 RH1E6S04_0594.rest = RH1E6S04_0594.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0594.s0 :: RH1E6S04_0594.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0594.s0.t = ((22525601255 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0594.s0]
  have e1 : RH1E6S04_0594.sL.t = ((22530366384 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0594.sL]
  rw [e0, e1] at h
  exact h

theorem band_0595 : RS5.BandZeros ((22530366384 : ℝ) / 65536) ((22535159729 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0595.s0 RH1E6S04_0595.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0595.s0 RH1E6S04_0595.rest = RH1E6S04_0595.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0595.s0 :: RH1E6S04_0595.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0595.s0.t = ((22530366384 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0595.s0]
  have e1 : RH1E6S04_0595.sL.t = ((22535159729 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0595.sL]
  rw [e0, e1] at h
  exact h

theorem part_074_1 : RS5.BandZeros ((22525601255 : ℝ) / 65536) ((22535159729 : ℝ) / 65536) 254 := by
  have g0 := band_0594
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0595
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((22525601255 : ℝ) / 65536) ((22535159729 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_074_1 <;> assumption
