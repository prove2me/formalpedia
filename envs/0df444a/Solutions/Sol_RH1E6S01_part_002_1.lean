-- Prove2me | solution 1 for RH1E6S01.part_002_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T23:27:44.920805+00:00
-- url     : https://prove2.me/submissions/96a571b9-3d0b-4194-9e91-a541ff3ac2de

import Definitions.Def_RH1E6S01_D002_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0018 : RS5.BandZeros ((9923729278 : ℝ) / 65536) ((9928912057 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0018.s0 RH1E6S01_0018.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0018.s0 RH1E6S01_0018.rest = RH1E6S01_0018.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0018.s0 :: RH1E6S01_0018.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0018.s0.t = ((9923729278 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0018.s0]
  have e1 : RH1E6S01_0018.sL.t = ((9928912057 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0018.sL]
  rw [e0, e1] at h
  exact h

theorem band_0019 : RS5.BandZeros ((9928912057 : ℝ) / 65536) ((9934104770 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0019.s0 RH1E6S01_0019.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0019.s0 RH1E6S01_0019.rest = RH1E6S01_0019.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0019.s0 :: RH1E6S01_0019.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0019.s0.t = ((9928912057 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0019.s0]
  have e1 : RH1E6S01_0019.sL.t = ((9934104770 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0019.sL]
  rw [e0, e1] at h
  exact h

theorem part_002_1 : RS5.BandZeros ((9923729278 : ℝ) / 65536) ((9934104770 : ℝ) / 65536) 254 := by
  have g0 := band_0018
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0019
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((9923729278 : ℝ) / 65536) ((9934104770 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_002_1 <;> assumption
