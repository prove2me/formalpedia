-- Prove2me | solution 1 for RH1E6S17.part_067_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T23:23:35.885496+00:00
-- url     : https://prove2.me/submissions/29458c96-7307-4785-942f-b3c9cf455bad

import Definitions.Def_RH1E6S17_D067_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0540 : RS5.BandZeros ((64623315182 : ℝ) / 65536) ((64627677772 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0540.s0 RH1E6S17_0540.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0540.s0 RH1E6S17_0540.rest = RH1E6S17_0540.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0540.s0 :: RH1E6S17_0540.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0540.s0.t = ((64623315182 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0540.s0]
  have e1 : RH1E6S17_0540.sL.t = ((64627677772 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0540.sL]
  rw [e0, e1] at h
  exact h

theorem band_0541 : RS5.BandZeros ((64627677772 : ℝ) / 65536) ((64632057546 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0541.s0 RH1E6S17_0541.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0541.s0 RH1E6S17_0541.rest = RH1E6S17_0541.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0541.s0 :: RH1E6S17_0541.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0541.s0.t = ((64627677772 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0541.s0]
  have e1 : RH1E6S17_0541.sL.t = ((64632057546 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0541.sL]
  rw [e0, e1] at h
  exact h

theorem part_067_2 : RS5.BandZeros ((64623315182 : ℝ) / 65536) ((64632057546 : ℝ) / 65536) 254 := by
  have g0 := band_0540
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0541
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((64623315182 : ℝ) / 65536) ((64632057546 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_067_2 <;> assumption
