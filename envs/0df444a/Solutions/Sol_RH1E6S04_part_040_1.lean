-- Prove2me | solution 1 for RH1E6S04.part_040_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T09:55:23.713178+00:00
-- url     : https://prove2.me/submissions/e616e08c-c01d-497c-98e0-94ae7a3a7c50

import Definitions.Def_RH1E6S04_D040_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0322 : RS5.BandZeros ((21218226775 : ℝ) / 65536) ((21223037136 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0322.s0 RH1E6S04_0322.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0322.s0 RH1E6S04_0322.rest = RH1E6S04_0322.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0322.s0 :: RH1E6S04_0322.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0322.s0.t = ((21218226775 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0322.s0]
  have e1 : RH1E6S04_0322.sL.t = ((21223037136 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0322.sL]
  rw [e0, e1] at h
  exact h

theorem band_0323 : RS5.BandZeros ((21223037136 : ℝ) / 65536) ((21227856885 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0323.s0 RH1E6S04_0323.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0323.s0 RH1E6S04_0323.rest = RH1E6S04_0323.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0323.s0 :: RH1E6S04_0323.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0323.s0.t = ((21223037136 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0323.s0]
  have e1 : RH1E6S04_0323.sL.t = ((21227856885 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0323.sL]
  rw [e0, e1] at h
  exact h

theorem part_040_1 : RS5.BandZeros ((21218226775 : ℝ) / 65536) ((21227856885 : ℝ) / 65536) 254 := by
  have g0 := band_0322
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0323
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((21218226775 : ℝ) / 65536) ((21227856885 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_040_1 <;> assumption
