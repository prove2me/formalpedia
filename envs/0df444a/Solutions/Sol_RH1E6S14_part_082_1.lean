-- Prove2me | solution 1 for RH1E6S14.part_082_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T07:07:59.788856+00:00
-- url     : https://prove2.me/submissions/64fb5902-f81a-43b1-92d9-d140d9770260

import Definitions.Def_RH1E6S14_D082_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0658 : RS5.BandZeros ((55349422065 : ℝ) / 65536) ((55353845971 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0658.s0 RH1E6S14_0658.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0658.s0 RH1E6S14_0658.rest = RH1E6S14_0658.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0658.s0 :: RH1E6S14_0658.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0658.s0.t = ((55349422065 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0658.s0]
  have e1 : RH1E6S14_0658.sL.t = ((55353845971 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0658.sL]
  rw [e0, e1] at h
  exact h

theorem band_0659 : RS5.BandZeros ((55353845971 : ℝ) / 65536) ((55358287122 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0659.s0 RH1E6S14_0659.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0659.s0 RH1E6S14_0659.rest = RH1E6S14_0659.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0659.s0 :: RH1E6S14_0659.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0659.s0.t = ((55353845971 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0659.s0]
  have e1 : RH1E6S14_0659.sL.t = ((55358287122 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0659.sL]
  rw [e0, e1] at h
  exact h

theorem part_082_1 : RS5.BandZeros ((55349422065 : ℝ) / 65536) ((55358287122 : ℝ) / 65536) 254 := by
  have g0 := band_0658
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0659
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((55349422065 : ℝ) / 65536) ((55358287122 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_082_1 <;> assumption
