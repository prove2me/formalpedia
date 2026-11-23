-- Prove2me | solution 1 for RH1E6S15.part_040_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T10:14:39.568458+00:00
-- url     : https://prove2.me/submissions/7ed4a4f9-5203-4153-a35d-5887474fac1d

import Definitions.Def_RH1E6S15_D040_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0322 : RS5.BandZeros ((57129247536 : ℝ) / 65536) ((57133691795 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0322.s0 RH1E6S15_0322.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0322.s0 RH1E6S15_0322.rest = RH1E6S15_0322.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0322.s0 :: RH1E6S15_0322.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0322.s0.t = ((57129247536 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0322.s0]
  have e1 : RH1E6S15_0322.sL.t = ((57133691795 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0322.sL]
  rw [e0, e1] at h
  exact h

theorem band_0323 : RS5.BandZeros ((57133691795 : ℝ) / 65536) ((57138093566 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0323.s0 RH1E6S15_0323.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0323.s0 RH1E6S15_0323.rest = RH1E6S15_0323.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0323.s0 :: RH1E6S15_0323.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0323.s0.t = ((57133691795 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0323.s0]
  have e1 : RH1E6S15_0323.sL.t = ((57138093566 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0323.sL]
  rw [e0, e1] at h
  exact h

theorem part_040_1 : RS5.BandZeros ((57129247536 : ℝ) / 65536) ((57138093566 : ℝ) / 65536) 254 := by
  have g0 := band_0322
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0323
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((57129247536 : ℝ) / 65536) ((57138093566 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_040_1 <;> assumption
