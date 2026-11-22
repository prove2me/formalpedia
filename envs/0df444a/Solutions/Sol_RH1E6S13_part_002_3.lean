-- Prove2me | solution 1 for RH1E6S13.part_002_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T17:54:28.496938+00:00
-- url     : https://prove2.me/submissions/df9f720d-2760-46b7-9dce-4393eadefab3

import Definitions.Def_RH1E6S13_D002_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0022 : RS5.BandZeros ((49250415248 : ℝ) / 65536) ((49254879195 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0022.s0 RH1E6S13_0022.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0022.s0 RH1E6S13_0022.rest = RH1E6S13_0022.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0022.s0 :: RH1E6S13_0022.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0022.s0.t = ((49250415248 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0022.s0]
  have e1 : RH1E6S13_0022.sL.t = ((49254879195 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0022.sL]
  rw [e0, e1] at h
  exact h

theorem band_0023 : RS5.BandZeros ((49254879195 : ℝ) / 65536) ((49259369522 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0023.s0 RH1E6S13_0023.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0023.s0 RH1E6S13_0023.rest = RH1E6S13_0023.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0023.s0 :: RH1E6S13_0023.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0023.s0.t = ((49254879195 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0023.s0]
  have e1 : RH1E6S13_0023.sL.t = ((49259369522 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0023.sL]
  rw [e0, e1] at h
  exact h

theorem part_002_3 : RS5.BandZeros ((49250415248 : ℝ) / 65536) ((49259369522 : ℝ) / 65536) 254 := by
  have g0 := band_0022
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0023
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((49250415248 : ℝ) / 65536) ((49259369522 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_002_3 <;> assumption
