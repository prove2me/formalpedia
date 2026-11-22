-- Prove2me | solution 1 for RH1E6S12.part_090_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T17:42:28.413442+00:00
-- url     : https://prove2.me/submissions/a9524bed-b2a6-4731-b7cd-855716d5506c

import Definitions.Def_RH1E6S12_D090_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0726 : RS5.BandZeros ((49132565962 : ℝ) / 65536) ((49137052834 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0726.s0 RH1E6S12_0726.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0726.s0 RH1E6S12_0726.rest = RH1E6S12_0726.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0726.s0 :: RH1E6S12_0726.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0726.s0.t = ((49132565962 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0726.s0]
  have e1 : RH1E6S12_0726.sL.t = ((49137052834 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0726.sL]
  rw [e0, e1] at h
  exact h

theorem band_0727 : RS5.BandZeros ((49137052834 : ℝ) / 65536) ((49141508855 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0727.s0 RH1E6S12_0727.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0727.s0 RH1E6S12_0727.rest = RH1E6S12_0727.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0727.s0 :: RH1E6S12_0727.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0727.s0.t = ((49137052834 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0727.s0]
  have e1 : RH1E6S12_0727.sL.t = ((49141508855 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0727.sL]
  rw [e0, e1] at h
  exact h

theorem part_090_3 : RS5.BandZeros ((49132565962 : ℝ) / 65536) ((49141508855 : ℝ) / 65536) 254 := by
  have g0 := band_0726
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0727
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((49132565962 : ℝ) / 65536) ((49141508855 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_090_3 <;> assumption
