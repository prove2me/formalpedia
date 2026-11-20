-- Prove2me | solution 1 for RH1E6S01.part_069_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T01:44:17.331193+00:00
-- url     : https://prove2.me/submissions/7511c511-db22-411e-891e-33239993bc48

import Definitions.Def_RH1E6S01_D069_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0556 : RS5.BandZeros ((12677358208 : ℝ) / 65536) ((12682408252 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0556.s0 RH1E6S01_0556.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0556.s0 RH1E6S01_0556.rest = RH1E6S01_0556.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0556.s0 :: RH1E6S01_0556.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0556.s0.t = ((12677358208 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0556.s0]
  have e1 : RH1E6S01_0556.sL.t = ((12682408252 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0556.sL]
  rw [e0, e1] at h
  exact h

theorem band_0557 : RS5.BandZeros ((12682408252 : ℝ) / 65536) ((12687487982 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0557.s0 RH1E6S01_0557.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0557.s0 RH1E6S01_0557.rest = RH1E6S01_0557.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0557.s0 :: RH1E6S01_0557.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0557.s0.t = ((12682408252 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0557.s0]
  have e1 : RH1E6S01_0557.sL.t = ((12687487982 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0557.sL]
  rw [e0, e1] at h
  exact h

theorem part_069_2 : RS5.BandZeros ((12677358208 : ℝ) / 65536) ((12687487982 : ℝ) / 65536) 254 := by
  have g0 := band_0556
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0557
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((12677358208 : ℝ) / 65536) ((12687487982 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_069_2 <;> assumption
