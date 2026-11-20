-- Prove2me | solution 1 for RH1E6S00.part_035_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T21:56:37.617429+00:00
-- url     : https://prove2.me/submissions/35581a88-5c1b-4fb6-b375-8020fef4d700

import Definitions.Def_RH1E6S00_D035_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0280 : RS5.BandZeros ((8050608150 : ℝ) / 65536) ((8055900612 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0280.s0 RH1E6S00_0280.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0280.s0 RH1E6S00_0280.rest = RH1E6S00_0280.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0280.s0 :: RH1E6S00_0280.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0280.s0.t = ((8050608150 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0280.s0]
  have e1 : RH1E6S00_0280.sL.t = ((8055900612 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0280.sL]
  rw [e0, e1] at h
  exact h

theorem band_0281 : RS5.BandZeros ((8055900612 : ℝ) / 65536) ((8061192722 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0281.s0 RH1E6S00_0281.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0281.s0 RH1E6S00_0281.rest = RH1E6S00_0281.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0281.s0 :: RH1E6S00_0281.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0281.s0.t = ((8055900612 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0281.s0]
  have e1 : RH1E6S00_0281.sL.t = ((8061192722 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0281.sL]
  rw [e0, e1] at h
  exact h

theorem part_035_0 : RS5.BandZeros ((8050608150 : ℝ) / 65536) ((8061192722 : ℝ) / 65536) 254 := by
  have g0 := band_0280
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0281
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((8050608150 : ℝ) / 65536) ((8061192722 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_035_0 <;> assumption
