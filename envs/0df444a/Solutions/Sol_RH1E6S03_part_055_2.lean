-- Prove2me | solution 1 for RH1E6S03.part_055_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T07:17:04.190474+00:00
-- url     : https://prove2.me/submissions/99837059-cb1f-4cf1-966c-6e122f70a457

import Definitions.Def_RH1E6S03_D055_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0444 : RS5.BandZeros ((18563159146 : ℝ) / 65536) ((18568029507 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0444.s0 RH1E6S03_0444.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0444.s0 RH1E6S03_0444.rest = RH1E6S03_0444.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0444.s0 :: RH1E6S03_0444.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0444.s0.t = ((18563159146 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0444.s0]
  have e1 : RH1E6S03_0444.sL.t = ((18568029507 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0444.sL]
  rw [e0, e1] at h
  exact h

theorem band_0445 : RS5.BandZeros ((18568029507 : ℝ) / 65536) ((18572928566 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0445.s0 RH1E6S03_0445.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0445.s0 RH1E6S03_0445.rest = RH1E6S03_0445.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0445.s0 :: RH1E6S03_0445.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0445.s0.t = ((18568029507 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0445.s0]
  have e1 : RH1E6S03_0445.sL.t = ((18572928566 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0445.sL]
  rw [e0, e1] at h
  exact h

theorem part_055_2 : RS5.BandZeros ((18563159146 : ℝ) / 65536) ((18572928566 : ℝ) / 65536) 254 := by
  have g0 := band_0444
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0445
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((18563159146 : ℝ) / 65536) ((18572928566 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_055_2 <;> assumption
