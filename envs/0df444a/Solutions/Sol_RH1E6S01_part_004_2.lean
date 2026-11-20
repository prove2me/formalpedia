-- Prove2me | solution 1 for RH1E6S01.part_004_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T23:30:21.182098+00:00
-- url     : https://prove2.me/submissions/f10c8c94-e403-4aa7-9bcf-f630e17b7090

import Definitions.Def_RH1E6S01_D004_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0036 : RS5.BandZeros ((10016968242 : ℝ) / 65536) ((10022166609 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0036.s0 RH1E6S01_0036.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0036.s0 RH1E6S01_0036.rest = RH1E6S01_0036.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0036.s0 :: RH1E6S01_0036.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0036.s0.t = ((10016968242 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0036.s0]
  have e1 : RH1E6S01_0036.sL.t = ((10022166609 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0036.sL]
  rw [e0, e1] at h
  exact h

theorem band_0037 : RS5.BandZeros ((10022166609 : ℝ) / 65536) ((10027344325 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0037.s0 RH1E6S01_0037.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0037.s0 RH1E6S01_0037.rest = RH1E6S01_0037.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0037.s0 :: RH1E6S01_0037.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0037.s0.t = ((10022166609 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0037.s0]
  have e1 : RH1E6S01_0037.sL.t = ((10027344325 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0037.sL]
  rw [e0, e1] at h
  exact h

theorem part_004_2 : RS5.BandZeros ((10016968242 : ℝ) / 65536) ((10027344325 : ℝ) / 65536) 254 := by
  have g0 := band_0036
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0037
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((10016968242 : ℝ) / 65536) ((10027344325 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_004_2 <;> assumption
