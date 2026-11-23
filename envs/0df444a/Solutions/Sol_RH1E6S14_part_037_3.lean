-- Prove2me | solution 1 for RH1E6S14.part_037_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T04:43:48.534218+00:00
-- url     : https://prove2.me/submissions/51164106-43f5-4ad3-80a0-fa243db82cf3

import Definitions.Def_RH1E6S14_D037_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0302 : RS5.BandZeros ((53770934818 : ℝ) / 65536) ((53775384797 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0302.s0 RH1E6S14_0302.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0302.s0 RH1E6S14_0302.rest = RH1E6S14_0302.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0302.s0 :: RH1E6S14_0302.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0302.s0.t = ((53770934818 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0302.s0]
  have e1 : RH1E6S14_0302.sL.t = ((53775384797 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0302.sL]
  rw [e0, e1] at h
  exact h

theorem band_0303 : RS5.BandZeros ((53775384797 : ℝ) / 65536) ((53779825043 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0303.s0 RH1E6S14_0303.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0303.s0 RH1E6S14_0303.rest = RH1E6S14_0303.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0303.s0 :: RH1E6S14_0303.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0303.s0.t = ((53775384797 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0303.s0]
  have e1 : RH1E6S14_0303.sL.t = ((53779825043 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0303.sL]
  rw [e0, e1] at h
  exact h

theorem part_037_3 : RS5.BandZeros ((53770934818 : ℝ) / 65536) ((53779825043 : ℝ) / 65536) 254 := by
  have g0 := band_0302
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0303
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((53770934818 : ℝ) / 65536) ((53779825043 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_037_3 <;> assumption
