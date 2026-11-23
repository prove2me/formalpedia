-- Prove2me | solution 1 for RH1E6S14.part_037_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T04:40:46.442252+00:00
-- url     : https://prove2.me/submissions/05c67785-82ae-451c-afa0-b91cdf3169c2

import Definitions.Def_RH1E6S14_D037_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0296 : RS5.BandZeros ((53744299786 : ℝ) / 65536) ((53748757703 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0296.s0 RH1E6S14_0296.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0296.s0 RH1E6S14_0296.rest = RH1E6S14_0296.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0296.s0 :: RH1E6S14_0296.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0296.s0.t = ((53744299786 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0296.s0]
  have e1 : RH1E6S14_0296.sL.t = ((53748757703 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0296.sL]
  rw [e0, e1] at h
  exact h

theorem band_0297 : RS5.BandZeros ((53748757703 : ℝ) / 65536) ((53753182973 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0297.s0 RH1E6S14_0297.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0297.s0 RH1E6S14_0297.rest = RH1E6S14_0297.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0297.s0 :: RH1E6S14_0297.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0297.s0.t = ((53748757703 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0297.s0]
  have e1 : RH1E6S14_0297.sL.t = ((53753182973 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0297.sL]
  rw [e0, e1] at h
  exact h

theorem part_037_0 : RS5.BandZeros ((53744299786 : ℝ) / 65536) ((53753182973 : ℝ) / 65536) 254 := by
  have g0 := band_0296
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0297
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((53744299786 : ℝ) / 65536) ((53753182973 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_037_0 <;> assumption
