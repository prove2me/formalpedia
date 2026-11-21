-- Prove2me | solution 1 for RH1E6S07.part_028_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T00:14:30.164321+00:00
-- url     : https://prove2.me/submissions/d92a237d-5a28-44a7-a5d9-d39eb27390d1

import Definitions.Def_RH1E6S07_D028_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0224 : RS5.BandZeros ((30537421103 : ℝ) / 65536) ((30542079981 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0224.s0 RH1E6S07_0224.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0224.s0 RH1E6S07_0224.rest = RH1E6S07_0224.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0224.s0 :: RH1E6S07_0224.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0224.s0.t = ((30537421103 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0224.s0]
  have e1 : RH1E6S07_0224.sL.t = ((30542079981 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0224.sL]
  rw [e0, e1] at h
  exact h

theorem band_0225 : RS5.BandZeros ((30542079981 : ℝ) / 65536) ((30546736333 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0225.s0 RH1E6S07_0225.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0225.s0 RH1E6S07_0225.rest = RH1E6S07_0225.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0225.s0 :: RH1E6S07_0225.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0225.s0.t = ((30542079981 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0225.s0]
  have e1 : RH1E6S07_0225.sL.t = ((30546736333 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0225.sL]
  rw [e0, e1] at h
  exact h

theorem part_028_0 : RS5.BandZeros ((30537421103 : ℝ) / 65536) ((30546736333 : ℝ) / 65536) 254 := by
  have g0 := band_0224
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0225
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((30537421103 : ℝ) / 65536) ((30546736333 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_028_0 <;> assumption
