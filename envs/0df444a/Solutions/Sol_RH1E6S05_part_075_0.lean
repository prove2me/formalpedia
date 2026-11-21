-- Prove2me | solution 1 for RH1E6S05.part_075_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T16:15:34.437954+00:00
-- url     : https://prove2.me/submissions/13de7921-8dd8-4613-935e-c1a3daa45a62

import Definitions.Def_RH1E6S05_D075_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0600 : RS5.BandZeros ((25793299411 : ℝ) / 65536) ((25798024746 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0600.s0 RH1E6S05_0600.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0600.s0 RH1E6S05_0600.rest = RH1E6S05_0600.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0600.s0 :: RH1E6S05_0600.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0600.s0.t = ((25793299411 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0600.s0]
  have e1 : RH1E6S05_0600.sL.t = ((25798024746 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0600.sL]
  rw [e0, e1] at h
  exact h

theorem band_0601 : RS5.BandZeros ((25798024746 : ℝ) / 65536) ((25802768643 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0601.s0 RH1E6S05_0601.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0601.s0 RH1E6S05_0601.rest = RH1E6S05_0601.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0601.s0 :: RH1E6S05_0601.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0601.s0.t = ((25798024746 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0601.s0]
  have e1 : RH1E6S05_0601.sL.t = ((25802768643 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0601.sL]
  rw [e0, e1] at h
  exact h

theorem part_075_0 : RS5.BandZeros ((25793299411 : ℝ) / 65536) ((25802768643 : ℝ) / 65536) 254 := by
  have g0 := band_0600
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0601
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((25793299411 : ℝ) / 65536) ((25802768643 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_075_0 <;> assumption
