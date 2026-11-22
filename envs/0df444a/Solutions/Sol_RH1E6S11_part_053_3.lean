-- Prove2me | solution 1 for RH1E6S11.part_053_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T05:33:26.332773+00:00
-- url     : https://prove2.me/submissions/77d1332c-ef0b-4878-a690-812c398c4efe

import Definitions.Def_RH1E6S11_D053_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0430 : RS5.BandZeros ((44542073233 : ℝ) / 65536) ((44546584756 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0430.s0 RH1E6S11_0430.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0430.s0 RH1E6S11_0430.rest = RH1E6S11_0430.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0430.s0 :: RH1E6S11_0430.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0430.s0.t = ((44542073233 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0430.s0]
  have e1 : RH1E6S11_0430.sL.t = ((44546584756 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0430.sL]
  rw [e0, e1] at h
  exact h

theorem band_0431 : RS5.BandZeros ((44546584756 : ℝ) / 65536) ((44551096239 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0431.s0 RH1E6S11_0431.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0431.s0 RH1E6S11_0431.rest = RH1E6S11_0431.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0431.s0 :: RH1E6S11_0431.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0431.s0.t = ((44546584756 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0431.s0]
  have e1 : RH1E6S11_0431.sL.t = ((44551096239 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0431.sL]
  rw [e0, e1] at h
  exact h

theorem part_053_3 : RS5.BandZeros ((44542073233 : ℝ) / 65536) ((44551096239 : ℝ) / 65536) 254 := by
  have g0 := band_0430
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0431
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((44542073233 : ℝ) / 65536) ((44551096239 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_053_3 <;> assumption
