-- Prove2me | solution 1 for RH1E6S10.part_037_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T22:59:31.165051+00:00
-- url     : https://prove2.me/submissions/27ff3d32-bfce-46bd-99ba-e74703ef2f80

import Definitions.Def_RH1E6S10_D037_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0300 : RS5.BandZeros ((40687752274 : ℝ) / 65536) ((40692299298 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0300.s0 RH1E6S10_0300.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0300.s0 RH1E6S10_0300.rest = RH1E6S10_0300.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0300.s0 :: RH1E6S10_0300.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0300.s0.t = ((40687752274 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0300.s0]
  have e1 : RH1E6S10_0300.sL.t = ((40692299298 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0300.sL]
  rw [e0, e1] at h
  exact h

theorem band_0301 : RS5.BandZeros ((40692299298 : ℝ) / 65536) ((40696837328 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0301.s0 RH1E6S10_0301.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0301.s0 RH1E6S10_0301.rest = RH1E6S10_0301.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0301.s0 :: RH1E6S10_0301.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0301.s0.t = ((40692299298 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0301.s0]
  have e1 : RH1E6S10_0301.sL.t = ((40696837328 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0301.sL]
  rw [e0, e1] at h
  exact h

theorem part_037_2 : RS5.BandZeros ((40687752274 : ℝ) / 65536) ((40696837328 : ℝ) / 65536) 254 := by
  have g0 := band_0300
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0301
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((40687752274 : ℝ) / 65536) ((40696837328 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_037_2 <;> assumption
