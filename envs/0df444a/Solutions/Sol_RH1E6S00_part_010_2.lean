-- Prove2me | solution 1 for RH1E6S00.part_010_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T21:09:38.270726+00:00
-- url     : https://prove2.me/submissions/e99c2508-7ab7-42f5-a79c-b0d61e5b9aca

import Definitions.Def_RH1E6S00_D010_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0084 : RS5.BandZeros ((7006086167 : ℝ) / 65536) ((7011443528 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0084.s0 RH1E6S00_0084.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0084.s0 RH1E6S00_0084.rest = RH1E6S00_0084.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0084.s0 :: RH1E6S00_0084.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0084.s0.t = ((7006086167 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0084.s0]
  have e1 : RH1E6S00_0084.sL.t = ((7011443528 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0084.sL]
  rw [e0, e1] at h
  exact h

theorem band_0085 : RS5.BandZeros ((7011443528 : ℝ) / 65536) ((7016811035 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0085.s0 RH1E6S00_0085.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0085.s0 RH1E6S00_0085.rest = RH1E6S00_0085.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0085.s0 :: RH1E6S00_0085.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0085.s0.t = ((7011443528 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0085.s0]
  have e1 : RH1E6S00_0085.sL.t = ((7016811035 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0085.sL]
  rw [e0, e1] at h
  exact h

theorem part_010_2 : RS5.BandZeros ((7006086167 : ℝ) / 65536) ((7016811035 : ℝ) / 65536) 254 := by
  have g0 := band_0084
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0085
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((7006086167 : ℝ) / 65536) ((7016811035 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_010_2 <;> assumption
