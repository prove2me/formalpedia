-- Prove2me | solution 1 for RH1E6S13.part_004_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T18:00:11.192885+00:00
-- url     : https://prove2.me/submissions/3a25655f-79e8-46ce-bb29-1193e506bc7f

import Definitions.Def_RH1E6S13_D004_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0036 : RS5.BandZeros ((49313030617 : ℝ) / 65536) ((49317494079 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0036.s0 RH1E6S13_0036.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0036.s0 RH1E6S13_0036.rest = RH1E6S13_0036.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0036.s0 :: RH1E6S13_0036.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0036.s0.t = ((49313030617 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0036.s0]
  have e1 : RH1E6S13_0036.sL.t = ((49317494079 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0036.sL]
  rw [e0, e1] at h
  exact h

theorem band_0037 : RS5.BandZeros ((49317494079 : ℝ) / 65536) ((49321975114 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0037.s0 RH1E6S13_0037.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0037.s0 RH1E6S13_0037.rest = RH1E6S13_0037.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0037.s0 :: RH1E6S13_0037.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0037.s0.t = ((49317494079 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0037.s0]
  have e1 : RH1E6S13_0037.sL.t = ((49321975114 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0037.sL]
  rw [e0, e1] at h
  exact h

theorem part_004_2 : RS5.BandZeros ((49313030617 : ℝ) / 65536) ((49321975114 : ℝ) / 65536) 254 := by
  have g0 := band_0036
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0037
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((49313030617 : ℝ) / 65536) ((49321975114 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_004_2 <;> assumption
