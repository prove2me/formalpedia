-- Prove2me | solution 1 for RH1E6S15.part_050_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T10:56:01.611916+00:00
-- url     : https://prove2.me/submissions/e4dfff20-d498-4ba5-90ef-73f45869c12e

import Definitions.Def_RH1E6S15_D050_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0404 : RS5.BandZeros ((57491339280 : ℝ) / 65536) ((57495750674 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0404.s0 RH1E6S15_0404.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0404.s0 RH1E6S15_0404.rest = RH1E6S15_0404.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0404.s0 :: RH1E6S15_0404.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0404.s0.t = ((57491339280 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0404.s0]
  have e1 : RH1E6S15_0404.sL.t = ((57495750674 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0404.sL]
  rw [e0, e1] at h
  exact h

theorem band_0405 : RS5.BandZeros ((57495750674 : ℝ) / 65536) ((57500151266 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0405.s0 RH1E6S15_0405.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0405.s0 RH1E6S15_0405.rest = RH1E6S15_0405.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0405.s0 :: RH1E6S15_0405.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0405.s0.t = ((57495750674 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0405.s0]
  have e1 : RH1E6S15_0405.sL.t = ((57500151266 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0405.sL]
  rw [e0, e1] at h
  exact h

theorem part_050_2 : RS5.BandZeros ((57491339280 : ℝ) / 65536) ((57500151266 : ℝ) / 65536) 254 := by
  have g0 := band_0404
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0405
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((57491339280 : ℝ) / 65536) ((57500151266 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_050_2 <;> assumption
