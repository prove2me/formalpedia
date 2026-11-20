-- Prove2me | solution 1 for RH1E6S00.part_034_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T21:54:21.50345+00:00
-- url     : https://prove2.me/submissions/db8dd154-633d-4b15-bbd2-86924e9fe72b

import Definitions.Def_RH1E6S00_D034_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0272 : RS5.BandZeros ((8008250536 : ℝ) / 65536) ((8013561459 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0272.s0 RH1E6S00_0272.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0272.s0 RH1E6S00_0272.rest = RH1E6S00_0272.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0272.s0 :: RH1E6S00_0272.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0272.s0.t = ((8008250536 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0272.s0]
  have e1 : RH1E6S00_0272.sL.t = ((8013561459 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0272.sL]
  rw [e0, e1] at h
  exact h

theorem band_0273 : RS5.BandZeros ((8013561459 : ℝ) / 65536) ((8018856392 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0273.s0 RH1E6S00_0273.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0273.s0 RH1E6S00_0273.rest = RH1E6S00_0273.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0273.s0 :: RH1E6S00_0273.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0273.s0.t = ((8013561459 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0273.s0]
  have e1 : RH1E6S00_0273.sL.t = ((8018856392 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0273.sL]
  rw [e0, e1] at h
  exact h

theorem part_034_0 : RS5.BandZeros ((8008250536 : ℝ) / 65536) ((8018856392 : ℝ) / 65536) 254 := by
  have g0 := band_0272
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0273
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((8008250536 : ℝ) / 65536) ((8018856392 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_034_0 <;> assumption
