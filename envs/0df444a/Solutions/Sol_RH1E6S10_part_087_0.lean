-- Prove2me | solution 1 for RH1E6S10.part_087_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T02:52:38.210364+00:00
-- url     : https://prove2.me/submissions/9269c6cf-3a11-443e-8661-481af2769c94

import Definitions.Def_RH1E6S10_D087_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0696 : RS5.BandZeros ((42484981114 : ℝ) / 65536) ((42489502197 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0696.s0 RH1E6S10_0696.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0696.s0 RH1E6S10_0696.rest = RH1E6S10_0696.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0696.s0 :: RH1E6S10_0696.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0696.s0.t = ((42484981114 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0696.s0]
  have e1 : RH1E6S10_0696.sL.t = ((42489502197 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0696.sL]
  rw [e0, e1] at h
  exact h

theorem band_0697 : RS5.BandZeros ((42489502197 : ℝ) / 65536) ((42494023239 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0697.s0 RH1E6S10_0697.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0697.s0 RH1E6S10_0697.rest = RH1E6S10_0697.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0697.s0 :: RH1E6S10_0697.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0697.s0.t = ((42489502197 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0697.s0]
  have e1 : RH1E6S10_0697.sL.t = ((42494023239 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0697.sL]
  rw [e0, e1] at h
  exact h

theorem part_087_0 : RS5.BandZeros ((42484981114 : ℝ) / 65536) ((42494023239 : ℝ) / 65536) 254 := by
  have g0 := band_0696
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0697
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((42484981114 : ℝ) / 65536) ((42494023239 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_087_0 <;> assumption
