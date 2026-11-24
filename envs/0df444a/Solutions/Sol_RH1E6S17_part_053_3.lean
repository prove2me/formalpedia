-- Prove2me | solution 1 for RH1E6S17.part_053_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T22:38:39.995682+00:00
-- url     : https://prove2.me/submissions/5427dc0e-4b08-4689-a616-ec7838b2af21

import Definitions.Def_RH1E6S17_D053_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0430 : RS5.BandZeros ((64142332501 : ℝ) / 65536) ((64146706426 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0430.s0 RH1E6S17_0430.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0430.s0 RH1E6S17_0430.rest = RH1E6S17_0430.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0430.s0 :: RH1E6S17_0430.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0430.s0.t = ((64142332501 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0430.s0]
  have e1 : RH1E6S17_0430.sL.t = ((64146706426 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0430.sL]
  rw [e0, e1] at h
  exact h

theorem band_0431 : RS5.BandZeros ((64146706426 : ℝ) / 65536) ((64151071716 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0431.s0 RH1E6S17_0431.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0431.s0 RH1E6S17_0431.rest = RH1E6S17_0431.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0431.s0 :: RH1E6S17_0431.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0431.s0.t = ((64146706426 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0431.s0]
  have e1 : RH1E6S17_0431.sL.t = ((64151071716 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0431.sL]
  rw [e0, e1] at h
  exact h

theorem part_053_3 : RS5.BandZeros ((64142332501 : ℝ) / 65536) ((64151071716 : ℝ) / 65536) 254 := by
  have g0 := band_0430
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0431
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((64142332501 : ℝ) / 65536) ((64151071716 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_053_3 <;> assumption
