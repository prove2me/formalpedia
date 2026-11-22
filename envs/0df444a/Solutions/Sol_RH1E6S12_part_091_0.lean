-- Prove2me | solution 1 for RH1E6S12.part_091_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T17:45:36.603809+00:00
-- url     : https://prove2.me/submissions/fe0a7c32-e72f-4122-a2b7-df0332e5ca4c

import Definitions.Def_RH1E6S12_D091_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0728 : RS5.BandZeros ((49141508855 : ℝ) / 65536) ((49145990337 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0728.s0 RH1E6S12_0728.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0728.s0 RH1E6S12_0728.rest = RH1E6S12_0728.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0728.s0 :: RH1E6S12_0728.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0728.s0.t = ((49141508855 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0728.s0]
  have e1 : RH1E6S12_0728.sL.t = ((49145990337 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0728.sL]
  rw [e0, e1] at h
  exact h

theorem band_0729 : RS5.BandZeros ((49145990337 : ℝ) / 65536) ((49150449726 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0729.s0 RH1E6S12_0729.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0729.s0 RH1E6S12_0729.rest = RH1E6S12_0729.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0729.s0 :: RH1E6S12_0729.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0729.s0.t = ((49145990337 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0729.s0]
  have e1 : RH1E6S12_0729.sL.t = ((49150449726 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0729.sL]
  rw [e0, e1] at h
  exact h

theorem part_091_0 : RS5.BandZeros ((49141508855 : ℝ) / 65536) ((49150449726 : ℝ) / 65536) 254 := by
  have g0 := band_0728
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0729
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((49141508855 : ℝ) / 65536) ((49150449726 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_091_0 <;> assumption
