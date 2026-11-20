-- Prove2me | solution 1 for RH1E6S02.part_034_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T03:20:10.861363+00:00
-- url     : https://prove2.me/submissions/ca28e9fc-670e-431d-b665-085b8eda1680

import Definitions.Def_RH1E6S02_D034_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0274 : RS5.BandZeros ((14482495101 : ℝ) / 65536) ((14487485040 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0274.s0 RH1E6S02_0274.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0274.s0 RH1E6S02_0274.rest = RH1E6S02_0274.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0274.s0 :: RH1E6S02_0274.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0274.s0.t = ((14482495101 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0274.s0]
  have e1 : RH1E6S02_0274.sL.t = ((14487485040 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0274.sL]
  rw [e0, e1] at h
  exact h

theorem band_0275 : RS5.BandZeros ((14487485040 : ℝ) / 65536) ((14492473031 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0275.s0 RH1E6S02_0275.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0275.s0 RH1E6S02_0275.rest = RH1E6S02_0275.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0275.s0 :: RH1E6S02_0275.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0275.s0.t = ((14487485040 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0275.s0]
  have e1 : RH1E6S02_0275.sL.t = ((14492473031 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0275.sL]
  rw [e0, e1] at h
  exact h

theorem part_034_1 : RS5.BandZeros ((14482495101 : ℝ) / 65536) ((14492473031 : ℝ) / 65536) 254 := by
  have g0 := band_0274
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0275
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((14482495101 : ℝ) / 65536) ((14492473031 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_034_1 <;> assumption
