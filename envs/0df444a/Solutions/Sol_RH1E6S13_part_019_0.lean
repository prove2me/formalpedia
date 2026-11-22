-- Prove2me | solution 1 for RH1E6S13.part_019_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T21:24:19.192903+00:00
-- url     : https://prove2.me/submissions/34a0ce8a-25ae-4cdb-9e3d-1f7850d989c9

import Definitions.Def_RH1E6S13_D019_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0152 : RS5.BandZeros ((49831583141 : ℝ) / 65536) ((49836051410 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0152.s0 RH1E6S13_0152.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0152.s0 RH1E6S13_0152.rest = RH1E6S13_0152.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0152.s0 :: RH1E6S13_0152.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0152.s0.t = ((49831583141 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0152.s0]
  have e1 : RH1E6S13_0152.sL.t = ((49836051410 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0152.sL]
  rw [e0, e1] at h
  exact h

theorem band_0153 : RS5.BandZeros ((49836051410 : ℝ) / 65536) ((49840528440 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0153.s0 RH1E6S13_0153.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0153.s0 RH1E6S13_0153.rest = RH1E6S13_0153.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0153.s0 :: RH1E6S13_0153.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0153.s0.t = ((49836051410 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0153.s0]
  have e1 : RH1E6S13_0153.sL.t = ((49840528440 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0153.sL]
  rw [e0, e1] at h
  exact h

theorem part_019_0 : RS5.BandZeros ((49831583141 : ℝ) / 65536) ((49840528440 : ℝ) / 65536) 254 := by
  have g0 := band_0152
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0153
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((49831583141 : ℝ) / 65536) ((49840528440 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_019_0 <;> assumption
