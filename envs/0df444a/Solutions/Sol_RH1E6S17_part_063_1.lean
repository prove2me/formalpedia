-- Prove2me | solution 1 for RH1E6S17.part_063_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T23:07:33.399075+00:00
-- url     : https://prove2.me/submissions/f4e52c81-b95f-4801-bdde-6481eb401431

import Definitions.Def_RH1E6S17_D063_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0506 : RS5.BandZeros ((64474679869 : ℝ) / 65536) ((64479043299 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0506.s0 RH1E6S17_0506.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0506.s0 RH1E6S17_0506.rest = RH1E6S17_0506.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0506.s0 :: RH1E6S17_0506.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0506.s0.t = ((64474679869 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0506.s0]
  have e1 : RH1E6S17_0506.sL.t = ((64479043299 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0506.sL]
  rw [e0, e1] at h
  exact h

theorem band_0507 : RS5.BandZeros ((64479043299 : ℝ) / 65536) ((64483423915 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0507.s0 RH1E6S17_0507.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0507.s0 RH1E6S17_0507.rest = RH1E6S17_0507.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0507.s0 :: RH1E6S17_0507.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0507.s0.t = ((64479043299 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0507.s0]
  have e1 : RH1E6S17_0507.sL.t = ((64483423915 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0507.sL]
  rw [e0, e1] at h
  exact h

theorem part_063_1 : RS5.BandZeros ((64474679869 : ℝ) / 65536) ((64483423915 : ℝ) / 65536) 254 := by
  have g0 := band_0506
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0507
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((64474679869 : ℝ) / 65536) ((64483423915 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_063_1 <;> assumption
