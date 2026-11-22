-- Prove2me | solution 1 for RH1E6S11.part_009_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T03:26:27.187663+00:00
-- url     : https://prove2.me/submissions/0c419475-f219-49cb-86c8-941625ff7bc3

import Definitions.Def_RH1E6S11_D009_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0072 : RS5.BandZeros ((42924384303 : ℝ) / 65536) ((42928892452 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0072.s0 RH1E6S11_0072.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0072.s0 RH1E6S11_0072.rest = RH1E6S11_0072.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0072.s0 :: RH1E6S11_0072.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0072.s0.t = ((42924384303 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0072.s0]
  have e1 : RH1E6S11_0072.sL.t = ((42928892452 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0072.sL]
  rw [e0, e1] at h
  exact h

theorem band_0073 : RS5.BandZeros ((42928892452 : ℝ) / 65536) ((42933427286 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0073.s0 RH1E6S11_0073.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0073.s0 RH1E6S11_0073.rest = RH1E6S11_0073.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0073.s0 :: RH1E6S11_0073.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0073.s0.t = ((42928892452 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0073.s0]
  have e1 : RH1E6S11_0073.sL.t = ((42933427286 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0073.sL]
  rw [e0, e1] at h
  exact h

theorem part_009_0 : RS5.BandZeros ((42924384303 : ℝ) / 65536) ((42933427286 : ℝ) / 65536) 254 := by
  have g0 := band_0072
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0073
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((42924384303 : ℝ) / 65536) ((42933427286 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_009_0 <;> assumption
