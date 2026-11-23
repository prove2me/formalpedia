-- Prove2me | solution 1 for RH1E6S14.part_027_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T04:04:47.46712+00:00
-- url     : https://prove2.me/submissions/52c01659-3e17-4b06-bf9c-9cf9ef752586

import Definitions.Def_RH1E6S14_D027_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0216 : RS5.BandZeros ((53389023591 : ℝ) / 65536) ((53393478842 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0216.s0 RH1E6S14_0216.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0216.s0 RH1E6S14_0216.rest = RH1E6S14_0216.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0216.s0 :: RH1E6S14_0216.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0216.s0.t = ((53389023591 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0216.s0]
  have e1 : RH1E6S14_0216.sL.t = ((53393478842 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0216.sL]
  rw [e0, e1] at h
  exact h

theorem band_0217 : RS5.BandZeros ((53393478842 : ℝ) / 65536) ((53397908659 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0217.s0 RH1E6S14_0217.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0217.s0 RH1E6S14_0217.rest = RH1E6S14_0217.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0217.s0 :: RH1E6S14_0217.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0217.s0.t = ((53393478842 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0217.s0]
  have e1 : RH1E6S14_0217.sL.t = ((53397908659 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0217.sL]
  rw [e0, e1] at h
  exact h

theorem part_027_0 : RS5.BandZeros ((53389023591 : ℝ) / 65536) ((53397908659 : ℝ) / 65536) 254 := by
  have g0 := band_0216
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0217
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((53389023591 : ℝ) / 65536) ((53397908659 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_027_0 <;> assumption
