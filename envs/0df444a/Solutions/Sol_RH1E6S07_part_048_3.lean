-- Prove2me | solution 1 for RH1E6S07.part_048_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T01:13:37.359615+00:00
-- url     : https://prove2.me/submissions/b42d0462-77e0-4d68-b0bf-6509fb354a8e

import Definitions.Def_RH1E6S07_D048_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0390 : RS5.BandZeros ((31310659922 : ℝ) / 65536) ((31315336897 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0390.s0 RH1E6S07_0390.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0390.s0 RH1E6S07_0390.rest = RH1E6S07_0390.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0390.s0 :: RH1E6S07_0390.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0390.s0.t = ((31310659922 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0390.s0]
  have e1 : RH1E6S07_0390.sL.t = ((31315336897 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0390.sL]
  rw [e0, e1] at h
  exact h

theorem band_0391 : RS5.BandZeros ((31315336897 : ℝ) / 65536) ((31319984184 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0391.s0 RH1E6S07_0391.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0391.s0 RH1E6S07_0391.rest = RH1E6S07_0391.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0391.s0 :: RH1E6S07_0391.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0391.s0.t = ((31315336897 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0391.s0]
  have e1 : RH1E6S07_0391.sL.t = ((31319984184 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0391.sL]
  rw [e0, e1] at h
  exact h

theorem part_048_3 : RS5.BandZeros ((31310659922 : ℝ) / 65536) ((31319984184 : ℝ) / 65536) 254 := by
  have g0 := band_0390
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0391
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((31310659922 : ℝ) / 65536) ((31319984184 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_048_3 <;> assumption
