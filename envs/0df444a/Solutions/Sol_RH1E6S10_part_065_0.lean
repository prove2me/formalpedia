-- Prove2me | solution 1 for RH1E6S10.part_065_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T01:53:25.806174+00:00
-- url     : https://prove2.me/submissions/53e63db8-501f-47b7-8767-cf37155d88e4

import Definitions.Def_RH1E6S10_D065_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0520 : RS5.BandZeros ((41687044137 : ℝ) / 65536) ((41691590522 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0520.s0 RH1E6S10_0520.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0520.s0 RH1E6S10_0520.rest = RH1E6S10_0520.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0520.s0 :: RH1E6S10_0520.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0520.s0.t = ((41687044137 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0520.s0]
  have e1 : RH1E6S10_0520.sL.t = ((41691590522 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0520.sL]
  rw [e0, e1] at h
  exact h

theorem band_0521 : RS5.BandZeros ((41691590522 : ℝ) / 65536) ((41696101135 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0521.s0 RH1E6S10_0521.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0521.s0 RH1E6S10_0521.rest = RH1E6S10_0521.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0521.s0 :: RH1E6S10_0521.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0521.s0.t = ((41691590522 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0521.s0]
  have e1 : RH1E6S10_0521.sL.t = ((41696101135 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0521.sL]
  rw [e0, e1] at h
  exact h

theorem part_065_0 : RS5.BandZeros ((41687044137 : ℝ) / 65536) ((41696101135 : ℝ) / 65536) 254 := by
  have g0 := band_0520
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0521
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((41687044137 : ℝ) / 65536) ((41696101135 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_065_0 <;> assumption
