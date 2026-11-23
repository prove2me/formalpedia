-- Prove2me | solution 1 for RH1E6S15.part_037_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T10:02:55.365847+00:00
-- url     : https://prove2.me/submissions/c71980b7-9925-47d7-876a-2d1f18312107

import Definitions.Def_RH1E6S15_D037_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0296 : RS5.BandZeros ((57014430863 : ℝ) / 65536) ((57018814064 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0296.s0 RH1E6S15_0296.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0296.s0 RH1E6S15_0296.rest = RH1E6S15_0296.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0296.s0 :: RH1E6S15_0296.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0296.s0.t = ((57014430863 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0296.s0]
  have e1 : RH1E6S15_0296.sL.t = ((57018814064 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0296.sL]
  rw [e0, e1] at h
  exact h

theorem band_0297 : RS5.BandZeros ((57018814064 : ℝ) / 65536) ((57023248337 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0297.s0 RH1E6S15_0297.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0297.s0 RH1E6S15_0297.rest = RH1E6S15_0297.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0297.s0 :: RH1E6S15_0297.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0297.s0.t = ((57018814064 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0297.s0]
  have e1 : RH1E6S15_0297.sL.t = ((57023248337 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0297.sL]
  rw [e0, e1] at h
  exact h

theorem part_037_0 : RS5.BandZeros ((57014430863 : ℝ) / 65536) ((57023248337 : ℝ) / 65536) 254 := by
  have g0 := band_0296
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0297
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((57014430863 : ℝ) / 65536) ((57023248337 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_037_0 <;> assumption
