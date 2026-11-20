-- Prove2me | solution 1 for RH1E6S01.part_005_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T23:32:37.609185+00:00
-- url     : https://prove2.me/submissions/fc562283-4f71-4b4f-be6f-8fd00c6dcae7

import Definitions.Def_RH1E6S01_D005_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0042 : RS5.BandZeros ((10048052544 : ℝ) / 65536) ((10053218748 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0042.s0 RH1E6S01_0042.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0042.s0 RH1E6S01_0042.rest = RH1E6S01_0042.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0042.s0 :: RH1E6S01_0042.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0042.s0.t = ((10048052544 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0042.s0]
  have e1 : RH1E6S01_0042.sL.t = ((10053218748 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0042.sL]
  rw [e0, e1] at h
  exact h

theorem band_0043 : RS5.BandZeros ((10053218748 : ℝ) / 65536) ((10058384690 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0043.s0 RH1E6S01_0043.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0043.s0 RH1E6S01_0043.rest = RH1E6S01_0043.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0043.s0 :: RH1E6S01_0043.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0043.s0.t = ((10053218748 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0043.s0]
  have e1 : RH1E6S01_0043.sL.t = ((10058384690 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0043.sL]
  rw [e0, e1] at h
  exact h

theorem part_005_1 : RS5.BandZeros ((10048052544 : ℝ) / 65536) ((10058384690 : ℝ) / 65536) 254 := by
  have g0 := band_0042
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0043
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((10048052544 : ℝ) / 65536) ((10058384690 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_005_1 <;> assumption
