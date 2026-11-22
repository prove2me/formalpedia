-- Prove2me | solution 1 for RH1E6S12.part_089_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T17:39:20.926084+00:00
-- url     : https://prove2.me/submissions/94ff95e3-005e-40c2-b732-c6a2dc2b8cb3

import Definitions.Def_RH1E6S12_D089_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0718 : RS5.BandZeros ((49096767136 : ℝ) / 65536) ((49101236089 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0718.s0 RH1E6S12_0718.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0718.s0 RH1E6S12_0718.rest = RH1E6S12_0718.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0718.s0 :: RH1E6S12_0718.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0718.s0.t = ((49096767136 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0718.s0]
  have e1 : RH1E6S12_0718.sL.t = ((49101236089 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0718.sL]
  rw [e0, e1] at h
  exact h

theorem band_0719 : RS5.BandZeros ((49101236089 : ℝ) / 65536) ((49105711036 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0719.s0 RH1E6S12_0719.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0719.s0 RH1E6S12_0719.rest = RH1E6S12_0719.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0719.s0 :: RH1E6S12_0719.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0719.s0.t = ((49101236089 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0719.s0]
  have e1 : RH1E6S12_0719.sL.t = ((49105711036 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0719.sL]
  rw [e0, e1] at h
  exact h

theorem part_089_3 : RS5.BandZeros ((49096767136 : ℝ) / 65536) ((49105711036 : ℝ) / 65536) 254 := by
  have g0 := band_0718
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0719
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((49096767136 : ℝ) / 65536) ((49105711036 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_089_3 <;> assumption
