-- Prove2me | solution 1 for RH1E6S17.part_035_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T21:32:38.473747+00:00
-- url     : https://prove2.me/submissions/92cfcc7b-3d1f-41ff-8cf6-d6175af183bb

import Definitions.Def_RH1E6S17_D035_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0282 : RS5.BandZeros ((63494706745 : ℝ) / 65536) ((63499101620 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0282.s0 RH1E6S17_0282.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0282.s0 RH1E6S17_0282.rest = RH1E6S17_0282.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0282.s0 :: RH1E6S17_0282.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0282.s0.t = ((63494706745 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0282.s0]
  have e1 : RH1E6S17_0282.sL.t = ((63499101620 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0282.sL]
  rw [e0, e1] at h
  exact h

theorem band_0283 : RS5.BandZeros ((63499101620 : ℝ) / 65536) ((63503462001 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0283.s0 RH1E6S17_0283.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0283.s0 RH1E6S17_0283.rest = RH1E6S17_0283.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0283.s0 :: RH1E6S17_0283.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0283.s0.t = ((63499101620 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0283.s0]
  have e1 : RH1E6S17_0283.sL.t = ((63503462001 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0283.sL]
  rw [e0, e1] at h
  exact h

theorem part_035_1 : RS5.BandZeros ((63494706745 : ℝ) / 65536) ((63503462001 : ℝ) / 65536) 254 := by
  have g0 := band_0282
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0283
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((63494706745 : ℝ) / 65536) ((63503462001 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_035_1 <;> assumption
