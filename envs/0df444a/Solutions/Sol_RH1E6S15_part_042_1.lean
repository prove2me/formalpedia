-- Prove2me | solution 1 for RH1E6S15.part_042_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T10:23:31.553707+00:00
-- url     : https://prove2.me/submissions/acdbfe9a-0cd4-4957-b2c0-d653e1184f31

import Definitions.Def_RH1E6S15_D042_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0338 : RS5.BandZeros ((57199916656 : ℝ) / 65536) ((57204332513 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0338.s0 RH1E6S15_0338.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0338.s0 RH1E6S15_0338.rest = RH1E6S15_0338.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0338.s0 :: RH1E6S15_0338.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0338.s0.t = ((57199916656 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0338.s0]
  have e1 : RH1E6S15_0338.sL.t = ((57204332513 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0338.sL]
  rw [e0, e1] at h
  exact h

theorem band_0339 : RS5.BandZeros ((57204332513 : ℝ) / 65536) ((57208751425 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0339.s0 RH1E6S15_0339.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0339.s0 RH1E6S15_0339.rest = RH1E6S15_0339.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0339.s0 :: RH1E6S15_0339.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0339.s0.t = ((57204332513 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0339.s0]
  have e1 : RH1E6S15_0339.sL.t = ((57208751425 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0339.sL]
  rw [e0, e1] at h
  exact h

theorem part_042_1 : RS5.BandZeros ((57199916656 : ℝ) / 65536) ((57208751425 : ℝ) / 65536) 254 := by
  have g0 := band_0338
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0339
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((57199916656 : ℝ) / 65536) ((57208751425 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_042_1 <;> assumption
