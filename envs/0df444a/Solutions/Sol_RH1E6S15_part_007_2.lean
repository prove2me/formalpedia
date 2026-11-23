-- Prove2me | solution 1 for RH1E6S15.part_007_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T08:13:33.262035+00:00
-- url     : https://prove2.me/submissions/d2622ede-7230-40bb-ba82-8f3b0cd63dd1

import Definitions.Def_RH1E6S15_D007_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0060 : RS5.BandZeros ((55971089894 : ℝ) / 65536) ((55975512043 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0060.s0 RH1E6S15_0060.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0060.s0 RH1E6S15_0060.rest = RH1E6S15_0060.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0060.s0 :: RH1E6S15_0060.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0060.s0.t = ((55971089894 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0060.s0]
  have e1 : RH1E6S15_0060.sL.t = ((55975512043 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0060.sL]
  rw [e0, e1] at h
  exact h

theorem band_0061 : RS5.BandZeros ((55975512043 : ℝ) / 65536) ((55979921144 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0061.s0 RH1E6S15_0061.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0061.s0 RH1E6S15_0061.rest = RH1E6S15_0061.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0061.s0 :: RH1E6S15_0061.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0061.s0.t = ((55975512043 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0061.s0]
  have e1 : RH1E6S15_0061.sL.t = ((55979921144 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0061.sL]
  rw [e0, e1] at h
  exact h

theorem part_007_2 : RS5.BandZeros ((55971089894 : ℝ) / 65536) ((55979921144 : ℝ) / 65536) 254 := by
  have g0 := band_0060
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0061
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((55971089894 : ℝ) / 65536) ((55979921144 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_007_2 <;> assumption
