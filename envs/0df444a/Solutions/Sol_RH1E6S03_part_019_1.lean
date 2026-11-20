-- Prove2me | solution 1 for RH1E6S03.part_019_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T05:56:10.283673+00:00
-- url     : https://prove2.me/submissions/82a4f65b-d5a3-48f1-ba8f-8422cfc18ab7

import Definitions.Def_RH1E6S03_D019_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0154 : RS5.BandZeros ((17142736069 : ℝ) / 65536) ((17147662230 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0154.s0 RH1E6S03_0154.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0154.s0 RH1E6S03_0154.rest = RH1E6S03_0154.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0154.s0 :: RH1E6S03_0154.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0154.s0.t = ((17142736069 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0154.s0]
  have e1 : RH1E6S03_0154.sL.t = ((17147662230 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0154.sL]
  rw [e0, e1] at h
  exact h

theorem band_0155 : RS5.BandZeros ((17147662230 : ℝ) / 65536) ((17152578579 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0155.s0 RH1E6S03_0155.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0155.s0 RH1E6S03_0155.rest = RH1E6S03_0155.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0155.s0 :: RH1E6S03_0155.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0155.s0.t = ((17147662230 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0155.s0]
  have e1 : RH1E6S03_0155.sL.t = ((17152578579 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0155.sL]
  rw [e0, e1] at h
  exact h

theorem part_019_1 : RS5.BandZeros ((17142736069 : ℝ) / 65536) ((17152578579 : ℝ) / 65536) 254 := by
  have g0 := band_0154
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0155
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((17142736069 : ℝ) / 65536) ((17152578579 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_019_1 <;> assumption
