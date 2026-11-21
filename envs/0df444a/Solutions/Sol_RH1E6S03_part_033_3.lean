-- Prove2me | solution 1 for RH1E6S03.part_033_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T06:28:03.191906+00:00
-- url     : https://prove2.me/submissions/e5ba2194-09e1-4e42-9022-a53f4bda652e

import Definitions.Def_RH1E6S03_D033_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0270 : RS5.BandZeros ((17712185891 : ℝ) / 65536) ((17717087317 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0270.s0 RH1E6S03_0270.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0270.s0 RH1E6S03_0270.rest = RH1E6S03_0270.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0270.s0 :: RH1E6S03_0270.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0270.s0.t = ((17712185891 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0270.s0]
  have e1 : RH1E6S03_0270.sL.t = ((17717087317 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0270.sL]
  rw [e0, e1] at h
  exact h

theorem band_0271 : RS5.BandZeros ((17717087317 : ℝ) / 65536) ((17721988617 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0271.s0 RH1E6S03_0271.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0271.s0 RH1E6S03_0271.rest = RH1E6S03_0271.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0271.s0 :: RH1E6S03_0271.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0271.s0.t = ((17717087317 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0271.s0]
  have e1 : RH1E6S03_0271.sL.t = ((17721988617 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0271.sL]
  rw [e0, e1] at h
  exact h

theorem part_033_3 : RS5.BandZeros ((17712185891 : ℝ) / 65536) ((17721988617 : ℝ) / 65536) 254 := by
  have g0 := band_0270
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0271
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((17712185891 : ℝ) / 65536) ((17721988617 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_033_3 <;> assumption
