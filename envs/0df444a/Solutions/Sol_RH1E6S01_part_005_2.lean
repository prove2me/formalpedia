-- Prove2me | solution 1 for RH1E6S01.part_005_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T23:34:51.963285+00:00
-- url     : https://prove2.me/submissions/3b1ae430-1833-4005-96c3-766a15ae454d

import Definitions.Def_RH1E6S01_D005_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0044 : RS5.BandZeros ((10058384690 : ℝ) / 65536) ((10063580935 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0044.s0 RH1E6S01_0044.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0044.s0 RH1E6S01_0044.rest = RH1E6S01_0044.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0044.s0 :: RH1E6S01_0044.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0044.s0.t = ((10058384690 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0044.s0]
  have e1 : RH1E6S01_0044.sL.t = ((10063580935 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0044.sL]
  rw [e0, e1] at h
  exact h

theorem band_0045 : RS5.BandZeros ((10063580935 : ℝ) / 65536) ((10068746350 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0045.s0 RH1E6S01_0045.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0045.s0 RH1E6S01_0045.rest = RH1E6S01_0045.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0045.s0 :: RH1E6S01_0045.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0045.s0.t = ((10063580935 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0045.s0]
  have e1 : RH1E6S01_0045.sL.t = ((10068746350 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0045.sL]
  rw [e0, e1] at h
  exact h

theorem part_005_2 : RS5.BandZeros ((10058384690 : ℝ) / 65536) ((10068746350 : ℝ) / 65536) 254 := by
  have g0 := band_0044
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0045
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((10058384690 : ℝ) / 65536) ((10068746350 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_005_2 <;> assumption
