-- Prove2me | solution 1 for RH1E6S02.part_014_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T02:39:20.873614+00:00
-- url     : https://prove2.me/submissions/cc812761-518b-46bb-b436-6dbfbdcc2cfd

import Definitions.Def_RH1E6S02_D014_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0116 : RS5.BandZeros ((13691061757 : ℝ) / 65536) ((13696068768 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0116.s0 RH1E6S02_0116.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0116.s0 RH1E6S02_0116.rest = RH1E6S02_0116.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0116.s0 :: RH1E6S02_0116.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0116.s0.t = ((13691061757 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0116.s0]
  have e1 : RH1E6S02_0116.sL.t = ((13696068768 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0116.sL]
  rw [e0, e1] at h
  exact h

theorem band_0117 : RS5.BandZeros ((13696068768 : ℝ) / 65536) ((13701110993 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0117.s0 RH1E6S02_0117.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0117.s0 RH1E6S02_0117.rest = RH1E6S02_0117.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0117.s0 :: RH1E6S02_0117.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0117.s0.t = ((13696068768 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0117.s0]
  have e1 : RH1E6S02_0117.sL.t = ((13701110993 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0117.sL]
  rw [e0, e1] at h
  exact h

theorem part_014_2 : RS5.BandZeros ((13691061757 : ℝ) / 65536) ((13701110993 : ℝ) / 65536) 254 := by
  have g0 := band_0116
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0117
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((13691061757 : ℝ) / 65536) ((13701110993 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_014_2 <;> assumption
