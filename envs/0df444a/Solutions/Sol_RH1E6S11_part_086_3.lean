-- Prove2me | solution 1 for RH1E6S11.part_086_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T07:10:15.708893+00:00
-- url     : https://prove2.me/submissions/f5a4b56f-164e-4362-9a0d-4dcebf0018e8

import Definitions.Def_RH1E6S11_D086_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0694 : RS5.BandZeros ((45731761905 : ℝ) / 65536) ((45736263192 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0694.s0 RH1E6S11_0694.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0694.s0 RH1E6S11_0694.rest = RH1E6S11_0694.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0694.s0 :: RH1E6S11_0694.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0694.s0.t = ((45731761905 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0694.s0]
  have e1 : RH1E6S11_0694.sL.t = ((45736263192 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0694.sL]
  rw [e0, e1] at h
  exact h

theorem band_0695 : RS5.BandZeros ((45736263192 : ℝ) / 65536) ((45740773303 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0695.s0 RH1E6S11_0695.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0695.s0 RH1E6S11_0695.rest = RH1E6S11_0695.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0695.s0 :: RH1E6S11_0695.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0695.s0.t = ((45736263192 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0695.s0]
  have e1 : RH1E6S11_0695.sL.t = ((45740773303 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0695.sL]
  rw [e0, e1] at h
  exact h

theorem part_086_3 : RS5.BandZeros ((45731761905 : ℝ) / 65536) ((45740773303 : ℝ) / 65536) 254 := by
  have g0 := band_0694
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0695
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((45731761905 : ℝ) / 65536) ((45740773303 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_086_3 <;> assumption
