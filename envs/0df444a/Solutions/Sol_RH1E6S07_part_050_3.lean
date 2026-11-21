-- Prove2me | solution 1 for RH1E6S07.part_050_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T01:19:16.836184+00:00
-- url     : https://prove2.me/submissions/d681fb5d-4d71-4b44-97e6-a6ee6fc35ea7

import Definitions.Def_RH1E6S07_D050_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0406 : RS5.BandZeros ((31385132217 : ℝ) / 65536) ((31389762189 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0406.s0 RH1E6S07_0406.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0406.s0 RH1E6S07_0406.rest = RH1E6S07_0406.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0406.s0 :: RH1E6S07_0406.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0406.s0.t = ((31385132217 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0406.s0]
  have e1 : RH1E6S07_0406.sL.t = ((31389762189 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0406.sL]
  rw [e0, e1] at h
  exact h

theorem band_0407 : RS5.BandZeros ((31389762189 : ℝ) / 65536) ((31394428203 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0407.s0 RH1E6S07_0407.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0407.s0 RH1E6S07_0407.rest = RH1E6S07_0407.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0407.s0 :: RH1E6S07_0407.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0407.s0.t = ((31389762189 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0407.s0]
  have e1 : RH1E6S07_0407.sL.t = ((31394428203 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0407.sL]
  rw [e0, e1] at h
  exact h

theorem part_050_3 : RS5.BandZeros ((31385132217 : ℝ) / 65536) ((31394428203 : ℝ) / 65536) 254 := by
  have g0 := band_0406
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0407
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((31385132217 : ℝ) / 65536) ((31394428203 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_050_3 <;> assumption
