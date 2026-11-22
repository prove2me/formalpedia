-- Prove2me | solution 1 for RH1E6S13.part_002_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T17:51:35.537117+00:00
-- url     : https://prove2.me/submissions/c67a8302-a225-47c9-a8ee-c08fe6d22e19

import Definitions.Def_RH1E6S13_D002_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0016 : RS5.BandZeros ((49223586811 : ℝ) / 65536) ((49228059771 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0016.s0 RH1E6S13_0016.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0016.s0 RH1E6S13_0016.rest = RH1E6S13_0016.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0016.s0 :: RH1E6S13_0016.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0016.s0.t = ((49223586811 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0016.s0]
  have e1 : RH1E6S13_0016.sL.t = ((49228059771 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0016.sL]
  rw [e0, e1] at h
  exact h

theorem band_0017 : RS5.BandZeros ((49228059771 : ℝ) / 65536) ((49232523892 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0017.s0 RH1E6S13_0017.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0017.s0 RH1E6S13_0017.rest = RH1E6S13_0017.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0017.s0 :: RH1E6S13_0017.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0017.s0.t = ((49228059771 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0017.s0]
  have e1 : RH1E6S13_0017.sL.t = ((49232523892 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0017.sL]
  rw [e0, e1] at h
  exact h

theorem part_002_0 : RS5.BandZeros ((49223586811 : ℝ) / 65536) ((49232523892 : ℝ) / 65536) 254 := by
  have g0 := band_0016
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0017
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((49223586811 : ℝ) / 65536) ((49232523892 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_002_0 <;> assumption
