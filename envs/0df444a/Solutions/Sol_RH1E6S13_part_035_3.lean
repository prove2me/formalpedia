-- Prove2me | solution 1 for RH1E6S13.part_035_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T22:34:01.148896+00:00
-- url     : https://prove2.me/submissions/9c3d4398-ea85-4352-a962-d4ba049e171e

import Definitions.Def_RH1E6S13_D035_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0286 : RS5.BandZeros ((50430018879 : ℝ) / 65536) ((50434500169 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0286.s0 RH1E6S13_0286.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0286.s0 RH1E6S13_0286.rest = RH1E6S13_0286.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0286.s0 :: RH1E6S13_0286.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0286.s0.t = ((50430018879 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0286.s0]
  have e1 : RH1E6S13_0286.sL.t = ((50434500169 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0286.sL]
  rw [e0, e1] at h
  exact h

theorem band_0287 : RS5.BandZeros ((50434500169 : ℝ) / 65536) ((50438946278 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0287.s0 RH1E6S13_0287.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0287.s0 RH1E6S13_0287.rest = RH1E6S13_0287.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0287.s0 :: RH1E6S13_0287.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0287.s0.t = ((50434500169 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0287.s0]
  have e1 : RH1E6S13_0287.sL.t = ((50438946278 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0287.sL]
  rw [e0, e1] at h
  exact h

theorem part_035_3 : RS5.BandZeros ((50430018879 : ℝ) / 65536) ((50438946278 : ℝ) / 65536) 254 := by
  have g0 := band_0286
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0287
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((50430018879 : ℝ) / 65536) ((50438946278 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_035_3 <;> assumption
