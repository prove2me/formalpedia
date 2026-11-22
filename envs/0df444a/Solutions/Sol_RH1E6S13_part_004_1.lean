-- Prove2me | solution 1 for RH1E6S13.part_004_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T19:13:00.512592+00:00
-- url     : https://prove2.me/submissions/8e3024cc-a473-43ca-94a1-6e96514f7df4

import Definitions.Def_RH1E6S13_D004_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0034 : RS5.BandZeros ((49304085980 : ℝ) / 65536) ((49308549512 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0034.s0 RH1E6S13_0034.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0034.s0 RH1E6S13_0034.rest = RH1E6S13_0034.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0034.s0 :: RH1E6S13_0034.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0034.s0.t = ((49304085980 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0034.s0]
  have e1 : RH1E6S13_0034.sL.t = ((49308549512 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0034.sL]
  rw [e0, e1] at h
  exact h

theorem band_0035 : RS5.BandZeros ((49308549512 : ℝ) / 65536) ((49313030617 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0035.s0 RH1E6S13_0035.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0035.s0 RH1E6S13_0035.rest = RH1E6S13_0035.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0035.s0 :: RH1E6S13_0035.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0035.s0.t = ((49308549512 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0035.s0]
  have e1 : RH1E6S13_0035.sL.t = ((49313030617 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0035.sL]
  rw [e0, e1] at h
  exact h

theorem part_004_1 : RS5.BandZeros ((49304085980 : ℝ) / 65536) ((49313030617 : ℝ) / 65536) 254 := by
  have g0 := band_0034
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0035
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((49304085980 : ℝ) / 65536) ((49313030617 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_004_1 <;> assumption
