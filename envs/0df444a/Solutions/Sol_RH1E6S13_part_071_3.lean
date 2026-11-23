-- Prove2me | solution 1 for RH1E6S13.part_071_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T01:07:47.930687+00:00
-- url     : https://prove2.me/submissions/c26d0822-a0ad-4ce6-8184-261f1289627a

import Definitions.Def_RH1E6S13_D071_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0574 : RS5.BandZeros ((51714207662 : ℝ) / 65536) ((51718644282 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0574.s0 RH1E6S13_0574.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0574.s0 RH1E6S13_0574.rest = RH1E6S13_0574.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0574.s0 :: RH1E6S13_0574.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0574.s0.t = ((51714207662 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0574.s0]
  have e1 : RH1E6S13_0574.sL.t = ((51718644282 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0574.sL]
  rw [e0, e1] at h
  exact h

theorem band_0575 : RS5.BandZeros ((51718644282 : ℝ) / 65536) ((51723107174 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0575.s0 RH1E6S13_0575.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0575.s0 RH1E6S13_0575.rest = RH1E6S13_0575.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0575.s0 :: RH1E6S13_0575.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0575.s0.t = ((51718644282 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0575.s0]
  have e1 : RH1E6S13_0575.sL.t = ((51723107174 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0575.sL]
  rw [e0, e1] at h
  exact h

theorem part_071_3 : RS5.BandZeros ((51714207662 : ℝ) / 65536) ((51723107174 : ℝ) / 65536) 254 := by
  have g0 := band_0574
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0575
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((51714207662 : ℝ) / 65536) ((51723107174 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_071_3 <;> assumption
