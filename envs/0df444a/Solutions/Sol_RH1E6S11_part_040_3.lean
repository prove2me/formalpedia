-- Prove2me | solution 1 for RH1E6S11.part_040_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T04:56:34.832547+00:00
-- url     : https://prove2.me/submissions/35b91c5c-f323-49f3-9d0f-b2b55e1c77e6

import Definitions.Def_RH1E6S11_D040_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0326 : RS5.BandZeros ((44072658644 : ℝ) / 65536) ((44077174294 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0326.s0 RH1E6S11_0326.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0326.s0 RH1E6S11_0326.rest = RH1E6S11_0326.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0326.s0 :: RH1E6S11_0326.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0326.s0.t = ((44072658644 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0326.s0]
  have e1 : RH1E6S11_0326.sL.t = ((44077174294 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0326.sL]
  rw [e0, e1] at h
  exact h

theorem band_0327 : RS5.BandZeros ((44077174294 : ℝ) / 65536) ((44081689904 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0327.s0 RH1E6S11_0327.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0327.s0 RH1E6S11_0327.rest = RH1E6S11_0327.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0327.s0 :: RH1E6S11_0327.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0327.s0.t = ((44077174294 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0327.s0]
  have e1 : RH1E6S11_0327.sL.t = ((44081689904 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0327.sL]
  rw [e0, e1] at h
  exact h

theorem part_040_3 : RS5.BandZeros ((44072658644 : ℝ) / 65536) ((44081689904 : ℝ) / 65536) 254 := by
  have g0 := band_0326
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0327
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((44072658644 : ℝ) / 65536) ((44081689904 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_040_3 <;> assumption
