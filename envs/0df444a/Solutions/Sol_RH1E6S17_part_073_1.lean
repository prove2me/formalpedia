-- Prove2me | solution 1 for RH1E6S17.part_073_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T23:46:17.748798+00:00
-- url     : https://prove2.me/submissions/984b3ad8-a8c9-4827-8839-de56e9c0d359

import Definitions.Def_RH1E6S17_D073_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0586 : RS5.BandZeros ((64824355956 : ℝ) / 65536) ((64828734618 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0586.s0 RH1E6S17_0586.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0586.s0 RH1E6S17_0586.rest = RH1E6S17_0586.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0586.s0 :: RH1E6S17_0586.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0586.s0.t = ((64824355956 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0586.s0]
  have e1 : RH1E6S17_0586.sL.t = ((64828734618 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0586.sL]
  rw [e0, e1] at h
  exact h

theorem band_0587 : RS5.BandZeros ((64828734618 : ℝ) / 65536) ((64833104652 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0587.s0 RH1E6S17_0587.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0587.s0 RH1E6S17_0587.rest = RH1E6S17_0587.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0587.s0 :: RH1E6S17_0587.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0587.s0.t = ((64828734618 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0587.s0]
  have e1 : RH1E6S17_0587.sL.t = ((64833104652 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0587.sL]
  rw [e0, e1] at h
  exact h

theorem part_073_1 : RS5.BandZeros ((64824355956 : ℝ) / 65536) ((64833104652 : ℝ) / 65536) 254 := by
  have g0 := band_0586
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0587
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((64824355956 : ℝ) / 65536) ((64833104652 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_073_1 <;> assumption
