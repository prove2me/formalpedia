-- Prove2me | solution 1 for RH1E6S13.part_050_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T23:35:23.829801+00:00
-- url     : https://prove2.me/submissions/a88796fc-5594-407b-877c-5a3336417031

import Definitions.Def_RH1E6S13_D050_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0406 : RS5.BandZeros ((50965433896 : ℝ) / 65536) ((50969893592 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0406.s0 RH1E6S13_0406.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0406.s0 RH1E6S13_0406.rest = RH1E6S13_0406.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0406.s0 :: RH1E6S13_0406.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0406.s0.t = ((50965433896 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0406.s0]
  have e1 : RH1E6S13_0406.sL.t = ((50969893592 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0406.sL]
  rw [e0, e1] at h
  exact h

theorem band_0407 : RS5.BandZeros ((50969893592 : ℝ) / 65536) ((50974344477 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0407.s0 RH1E6S13_0407.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0407.s0 RH1E6S13_0407.rest = RH1E6S13_0407.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0407.s0 :: RH1E6S13_0407.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0407.s0.t = ((50969893592 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0407.s0]
  have e1 : RH1E6S13_0407.sL.t = ((50974344477 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0407.sL]
  rw [e0, e1] at h
  exact h

theorem part_050_3 : RS5.BandZeros ((50965433896 : ℝ) / 65536) ((50974344477 : ℝ) / 65536) 254 := by
  have g0 := band_0406
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0407
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((50965433896 : ℝ) / 65536) ((50974344477 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_050_3 <;> assumption
