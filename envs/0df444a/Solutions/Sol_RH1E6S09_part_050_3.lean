-- Prove2me | solution 1 for RH1E6S09.part_050_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T10:31:35.686579+00:00
-- url     : https://prove2.me/submissions/434416e8-b1f7-450d-b7e7-e7410d9baaa4

import Definitions.Def_RH1E6S09_D050_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0406 : RS5.BandZeros ((37906377417 : ℝ) / 65536) ((37910972619 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0406.s0 RH1E6S09_0406.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0406.s0 RH1E6S09_0406.rest = RH1E6S09_0406.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0406.s0 :: RH1E6S09_0406.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0406.s0.t = ((37906377417 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0406.s0]
  have e1 : RH1E6S09_0406.sL.t = ((37910972619 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0406.sL]
  rw [e0, e1] at h
  exact h

theorem band_0407 : RS5.BandZeros ((37910972619 : ℝ) / 65536) ((37915536492 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0407.s0 RH1E6S09_0407.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0407.s0 RH1E6S09_0407.rest = RH1E6S09_0407.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0407.s0 :: RH1E6S09_0407.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0407.s0.t = ((37910972619 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0407.s0]
  have e1 : RH1E6S09_0407.sL.t = ((37915536492 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0407.sL]
  rw [e0, e1] at h
  exact h

theorem part_050_3 : RS5.BandZeros ((37906377417 : ℝ) / 65536) ((37915536492 : ℝ) / 65536) 254 := by
  have g0 := band_0406
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0407
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((37906377417 : ℝ) / 65536) ((37915536492 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_050_3 <;> assumption
