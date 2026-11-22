-- Prove2me | solution 1 for RH1E6S12.part_089_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T17:39:18.829618+00:00
-- url     : https://prove2.me/submissions/15d317e1-9868-4ee7-a342-0c187c992dc6

import Definitions.Def_RH1E6S12_D089_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0716 : RS5.BandZeros ((49087816697 : ℝ) / 65536) ((49092288159 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0716.s0 RH1E6S12_0716.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0716.s0 RH1E6S12_0716.rest = RH1E6S12_0716.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0716.s0 :: RH1E6S12_0716.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0716.s0.t = ((49087816697 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0716.s0]
  have e1 : RH1E6S12_0716.sL.t = ((49092288159 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0716.sL]
  rw [e0, e1] at h
  exact h

theorem band_0717 : RS5.BandZeros ((49092288159 : ℝ) / 65536) ((49096767136 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0717.s0 RH1E6S12_0717.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0717.s0 RH1E6S12_0717.rest = RH1E6S12_0717.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0717.s0 :: RH1E6S12_0717.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0717.s0.t = ((49092288159 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0717.s0]
  have e1 : RH1E6S12_0717.sL.t = ((49096767136 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0717.sL]
  rw [e0, e1] at h
  exact h

theorem part_089_2 : RS5.BandZeros ((49087816697 : ℝ) / 65536) ((49096767136 : ℝ) / 65536) 254 := by
  have g0 := band_0716
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0717
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((49087816697 : ℝ) / 65536) ((49096767136 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_089_2 <;> assumption
