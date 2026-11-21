-- Prove2me | solution 1 for RH1E6S04.part_020_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T09:08:10.639124+00:00
-- url     : https://prove2.me/submissions/c6941892-44fb-48c9-b61a-5a8be4155066

import Definitions.Def_RH1E6S04_D020_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0160 : RS5.BandZeros ((20436067169 : ℝ) / 65536) ((20440884718 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0160.s0 RH1E6S04_0160.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0160.s0 RH1E6S04_0160.rest = RH1E6S04_0160.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0160.s0 :: RH1E6S04_0160.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0160.s0.t = ((20436067169 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0160.s0]
  have e1 : RH1E6S04_0160.sL.t = ((20440884718 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0160.sL]
  rw [e0, e1] at h
  exact h

theorem band_0161 : RS5.BandZeros ((20440884718 : ℝ) / 65536) ((20445711682 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0161.s0 RH1E6S04_0161.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0161.s0 RH1E6S04_0161.rest = RH1E6S04_0161.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0161.s0 :: RH1E6S04_0161.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0161.s0.t = ((20440884718 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0161.s0]
  have e1 : RH1E6S04_0161.sL.t = ((20445711682 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0161.sL]
  rw [e0, e1] at h
  exact h

theorem part_020_0 : RS5.BandZeros ((20436067169 : ℝ) / 65536) ((20445711682 : ℝ) / 65536) 254 := by
  have g0 := band_0160
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0161
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((20436067169 : ℝ) / 65536) ((20445711682 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_020_0 <;> assumption
