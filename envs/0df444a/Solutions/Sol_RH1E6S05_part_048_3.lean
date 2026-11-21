-- Prove2me | solution 1 for RH1E6S05.part_048_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T14:21:56.99812+00:00
-- url     : https://prove2.me/submissions/3780894a-40a7-41ab-9946-ee7c3efa70ea

import Definitions.Def_RH1E6S05_D048_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0390 : RS5.BandZeros ((24797240150 : ℝ) / 65536) ((24801978884 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0390.s0 RH1E6S05_0390.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0390.s0 RH1E6S05_0390.rest = RH1E6S05_0390.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0390.s0 :: RH1E6S05_0390.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0390.s0.t = ((24797240150 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0390.s0]
  have e1 : RH1E6S05_0390.sL.t = ((24801978884 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0390.sL]
  rw [e0, e1] at h
  exact h

theorem band_0391 : RS5.BandZeros ((24801978884 : ℝ) / 65536) ((24806752611 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0391.s0 RH1E6S05_0391.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0391.s0 RH1E6S05_0391.rest = RH1E6S05_0391.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0391.s0 :: RH1E6S05_0391.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0391.s0.t = ((24801978884 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0391.s0]
  have e1 : RH1E6S05_0391.sL.t = ((24806752611 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0391.sL]
  rw [e0, e1] at h
  exact h

theorem part_048_3 : RS5.BandZeros ((24797240150 : ℝ) / 65536) ((24806752611 : ℝ) / 65536) 254 := by
  have g0 := band_0390
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0391
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((24797240150 : ℝ) / 65536) ((24806752611 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_048_3 <;> assumption
