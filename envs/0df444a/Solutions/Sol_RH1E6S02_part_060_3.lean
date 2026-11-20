-- Prove2me | solution 1 for RH1E6S02.part_060_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T04:15:59.867508+00:00
-- url     : https://prove2.me/submissions/39000d0c-3534-4c90-9e46-1e88e4a2cd2c

import Definitions.Def_RH1E6S02_D060_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0486 : RS5.BandZeros ((15538008452 : ℝ) / 65536) ((15542960219 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0486.s0 RH1E6S02_0486.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0486.s0 RH1E6S02_0486.rest = RH1E6S02_0486.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0486.s0 :: RH1E6S02_0486.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0486.s0.t = ((15538008452 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0486.s0]
  have e1 : RH1E6S02_0486.sL.t = ((15542960219 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0486.sL]
  rw [e0, e1] at h
  exact h

theorem band_0487 : RS5.BandZeros ((15542960219 : ℝ) / 65536) ((15547933344 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0487.s0 RH1E6S02_0487.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0487.s0 RH1E6S02_0487.rest = RH1E6S02_0487.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0487.s0 :: RH1E6S02_0487.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0487.s0.t = ((15542960219 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0487.s0]
  have e1 : RH1E6S02_0487.sL.t = ((15547933344 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0487.sL]
  rw [e0, e1] at h
  exact h

theorem part_060_3 : RS5.BandZeros ((15538008452 : ℝ) / 65536) ((15547933344 : ℝ) / 65536) 254 := by
  have g0 := band_0486
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0487
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((15538008452 : ℝ) / 65536) ((15547933344 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_060_3 <;> assumption
