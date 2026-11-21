-- Prove2me | solution 1 for RH1E6S04.part_061_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T10:42:59.612241+00:00
-- url     : https://prove2.me/submissions/0be75e02-b618-434b-87fc-cf4618d07cd3

import Definitions.Def_RH1E6S04_D061_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0492 : RS5.BandZeros ((22036165528 : ℝ) / 65536) ((22040968635 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0492.s0 RH1E6S04_0492.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0492.s0 RH1E6S04_0492.rest = RH1E6S04_0492.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0492.s0 :: RH1E6S04_0492.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0492.s0.t = ((22036165528 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0492.s0]
  have e1 : RH1E6S04_0492.sL.t = ((22040968635 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0492.sL]
  rw [e0, e1] at h
  exact h

theorem band_0493 : RS5.BandZeros ((22040968635 : ℝ) / 65536) ((22045762192 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0493.s0 RH1E6S04_0493.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0493.s0 RH1E6S04_0493.rest = RH1E6S04_0493.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0493.s0 :: RH1E6S04_0493.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0493.s0.t = ((22040968635 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0493.s0]
  have e1 : RH1E6S04_0493.sL.t = ((22045762192 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0493.sL]
  rw [e0, e1] at h
  exact h

theorem part_061_2 : RS5.BandZeros ((22036165528 : ℝ) / 65536) ((22045762192 : ℝ) / 65536) 254 := by
  have g0 := band_0492
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0493
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((22036165528 : ℝ) / 65536) ((22045762192 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_061_2 <;> assumption
