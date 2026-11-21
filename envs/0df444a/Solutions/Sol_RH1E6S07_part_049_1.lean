-- Prove2me | solution 1 for RH1E6S07.part_049_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T01:16:16.587654+00:00
-- url     : https://prove2.me/submissions/044a4cd8-ebdc-4f30-8f1b-b359943ce6be

import Definitions.Def_RH1E6S07_D049_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0394 : RS5.BandZeros ((31329292799 : ℝ) / 65536) ((31333924318 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0394.s0 RH1E6S07_0394.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0394.s0 RH1E6S07_0394.rest = RH1E6S07_0394.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0394.s0 :: RH1E6S07_0394.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0394.s0.t = ((31329292799 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0394.s0]
  have e1 : RH1E6S07_0394.sL.t = ((31333924318 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0394.sL]
  rw [e0, e1] at h
  exact h

theorem band_0395 : RS5.BandZeros ((31333924318 : ℝ) / 65536) ((31338591543 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0395.s0 RH1E6S07_0395.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0395.s0 RH1E6S07_0395.rest = RH1E6S07_0395.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0395.s0 :: RH1E6S07_0395.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0395.s0.t = ((31333924318 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0395.s0]
  have e1 : RH1E6S07_0395.sL.t = ((31338591543 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0395.sL]
  rw [e0, e1] at h
  exact h

theorem part_049_1 : RS5.BandZeros ((31329292799 : ℝ) / 65536) ((31338591543 : ℝ) / 65536) 254 := by
  have g0 := band_0394
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0395
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((31329292799 : ℝ) / 65536) ((31338591543 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_049_1 <;> assumption
