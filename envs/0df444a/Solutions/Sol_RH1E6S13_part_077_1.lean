-- Prove2me | solution 1 for RH1E6S13.part_077_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T01:53:10.220824+00:00
-- url     : https://prove2.me/submissions/1c12395a-76c7-45ea-b1d0-ccf5e97f7124

import Definitions.Def_RH1E6S13_D077_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0618 : RS5.BandZeros ((51910150924 : ℝ) / 65536) ((51914603646 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0618.s0 RH1E6S13_0618.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0618.s0 RH1E6S13_0618.rest = RH1E6S13_0618.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0618.s0 :: RH1E6S13_0618.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0618.s0.t = ((51910150924 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0618.s0]
  have e1 : RH1E6S13_0618.sL.t = ((51914603646 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0618.sL]
  rw [e0, e1] at h
  exact h

theorem band_0619 : RS5.BandZeros ((51914603646 : ℝ) / 65536) ((51919056336 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0619.s0 RH1E6S13_0619.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0619.s0 RH1E6S13_0619.rest = RH1E6S13_0619.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0619.s0 :: RH1E6S13_0619.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0619.s0.t = ((51914603646 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0619.s0]
  have e1 : RH1E6S13_0619.sL.t = ((51919056336 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0619.sL]
  rw [e0, e1] at h
  exact h

theorem part_077_1 : RS5.BandZeros ((51910150924 : ℝ) / 65536) ((51919056336 : ℝ) / 65536) 254 := by
  have g0 := band_0618
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0619
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((51910150924 : ℝ) / 65536) ((51919056336 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_077_1 <;> assumption
