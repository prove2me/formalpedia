-- Prove2me | solution 1 for RH1E6S10.part_084_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T02:46:47.915384+00:00
-- url     : https://prove2.me/submissions/20605e0a-b116-462a-8a88-33c7a631a215

import Definitions.Def_RH1E6S10_D084_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0674 : RS5.BandZeros ((42385296012 : ℝ) / 65536) ((42389841428 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0674.s0 RH1E6S10_0674.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0674.s0 RH1E6S10_0674.rest = RH1E6S10_0674.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0674.s0 :: RH1E6S10_0674.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0674.s0.t = ((42385296012 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0674.s0]
  have e1 : RH1E6S10_0674.sL.t = ((42389841428 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0674.sL]
  rw [e0, e1] at h
  exact h

theorem band_0675 : RS5.BandZeros ((42389841428 : ℝ) / 65536) ((42394372309 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0675.s0 RH1E6S10_0675.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0675.s0 RH1E6S10_0675.rest = RH1E6S10_0675.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0675.s0 :: RH1E6S10_0675.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0675.s0.t = ((42389841428 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0675.s0]
  have e1 : RH1E6S10_0675.sL.t = ((42394372309 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0675.sL]
  rw [e0, e1] at h
  exact h

theorem part_084_1 : RS5.BandZeros ((42385296012 : ℝ) / 65536) ((42394372309 : ℝ) / 65536) 254 := by
  have g0 := band_0674
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0675
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((42385296012 : ℝ) / 65536) ((42394372309 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_084_1 <;> assumption
