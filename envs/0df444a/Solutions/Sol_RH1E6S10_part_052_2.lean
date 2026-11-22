-- Prove2me | solution 1 for RH1E6S10.part_052_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T01:19:46.89452+00:00
-- url     : https://prove2.me/submissions/fe26d451-9785-4b0f-96ad-e550ae8c0510

import Definitions.Def_RH1E6S10_D052_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0420 : RS5.BandZeros ((41233090444 : ℝ) / 65536) ((41237614330 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0420.s0 RH1E6S10_0420.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0420.s0 RH1E6S10_0420.rest = RH1E6S10_0420.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0420.s0 :: RH1E6S10_0420.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0420.s0.t = ((41233090444 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0420.s0]
  have e1 : RH1E6S10_0420.sL.t = ((41237614330 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0420.sL]
  rw [e0, e1] at h
  exact h

theorem band_0421 : RS5.BandZeros ((41237614330 : ℝ) / 65536) ((41242156053 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0421.s0 RH1E6S10_0421.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0421.s0 RH1E6S10_0421.rest = RH1E6S10_0421.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0421.s0 :: RH1E6S10_0421.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0421.s0.t = ((41237614330 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0421.s0]
  have e1 : RH1E6S10_0421.sL.t = ((41242156053 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0421.sL]
  rw [e0, e1] at h
  exact h

theorem part_052_2 : RS5.BandZeros ((41233090444 : ℝ) / 65536) ((41242156053 : ℝ) / 65536) 254 := by
  have g0 := band_0420
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0421
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((41233090444 : ℝ) / 65536) ((41242156053 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_052_2 <;> assumption
