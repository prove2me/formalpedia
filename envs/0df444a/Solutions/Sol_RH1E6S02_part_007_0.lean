-- Prove2me | solution 1 for RH1E6S02.part_007_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T02:22:36.440144+00:00
-- url     : https://prove2.me/submissions/56987712-e1f5-4100-a0c6-626e39993b43

import Definitions.Def_RH1E6S02_D007_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0056 : RS5.BandZeros ((13389362007 : ℝ) / 65536) ((13394413004 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0056.s0 RH1E6S02_0056.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0056.s0 RH1E6S02_0056.rest = RH1E6S02_0056.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0056.s0 :: RH1E6S02_0056.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0056.s0.t = ((13389362007 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0056.s0]
  have e1 : RH1E6S02_0056.sL.t = ((13394413004 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0056.sL]
  rw [e0, e1] at h
  exact h

theorem band_0057 : RS5.BandZeros ((13394413004 : ℝ) / 65536) ((13399447941 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0057.s0 RH1E6S02_0057.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0057.s0 RH1E6S02_0057.rest = RH1E6S02_0057.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0057.s0 :: RH1E6S02_0057.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0057.s0.t = ((13394413004 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0057.s0]
  have e1 : RH1E6S02_0057.sL.t = ((13399447941 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0057.sL]
  rw [e0, e1] at h
  exact h

theorem part_007_0 : RS5.BandZeros ((13389362007 : ℝ) / 65536) ((13399447941 : ℝ) / 65536) 254 := by
  have g0 := band_0056
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0057
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((13389362007 : ℝ) / 65536) ((13399447941 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_007_0 <;> assumption
