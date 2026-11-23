-- Prove2me | solution 1 for RH1E6S14.part_077_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T06:53:02.504561+00:00
-- url     : https://prove2.me/submissions/1d27a530-2d3b-4a64-b82a-77b5aebcbfd0

import Definitions.Def_RH1E6S14_D077_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0618 : RS5.BandZeros ((55172263421 : ℝ) / 65536) ((55176686089 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0618.s0 RH1E6S14_0618.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0618.s0 RH1E6S14_0618.rest = RH1E6S14_0618.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0618.s0 :: RH1E6S14_0618.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0618.s0.t = ((55172263421 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0618.s0]
  have e1 : RH1E6S14_0618.sL.t = ((55176686089 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0618.sL]
  rw [e0, e1] at h
  exact h

theorem band_0619 : RS5.BandZeros ((55176686089 : ℝ) / 65536) ((55181119613 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0619.s0 RH1E6S14_0619.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0619.s0 RH1E6S14_0619.rest = RH1E6S14_0619.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0619.s0 :: RH1E6S14_0619.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0619.s0.t = ((55176686089 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0619.s0]
  have e1 : RH1E6S14_0619.sL.t = ((55181119613 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0619.sL]
  rw [e0, e1] at h
  exact h

theorem part_077_1 : RS5.BandZeros ((55172263421 : ℝ) / 65536) ((55181119613 : ℝ) / 65536) 254 := by
  have g0 := band_0618
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0619
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((55172263421 : ℝ) / 65536) ((55181119613 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_077_1 <;> assumption
