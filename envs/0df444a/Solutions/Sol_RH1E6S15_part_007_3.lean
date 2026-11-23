-- Prove2me | solution 1 for RH1E6S15.part_007_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T08:13:35.282775+00:00
-- url     : https://prove2.me/submissions/0a809906-990e-40b0-9a11-316d1d2a88a0

import Definitions.Def_RH1E6S15_D007_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0062 : RS5.BandZeros ((55979921144 : ℝ) / 65536) ((55984353561 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0062.s0 RH1E6S15_0062.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0062.s0 RH1E6S15_0062.rest = RH1E6S15_0062.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0062.s0 :: RH1E6S15_0062.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0062.s0.t = ((55979921144 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0062.s0]
  have e1 : RH1E6S15_0062.sL.t = ((55984353561 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0062.sL]
  rw [e0, e1] at h
  exact h

theorem band_0063 : RS5.BandZeros ((55984353561 : ℝ) / 65536) ((55988782582 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0063.s0 RH1E6S15_0063.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0063.s0 RH1E6S15_0063.rest = RH1E6S15_0063.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0063.s0 :: RH1E6S15_0063.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0063.s0.t = ((55984353561 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0063.s0]
  have e1 : RH1E6S15_0063.sL.t = ((55988782582 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0063.sL]
  rw [e0, e1] at h
  exact h

theorem part_007_3 : RS5.BandZeros ((55979921144 : ℝ) / 65536) ((55988782582 : ℝ) / 65536) 254 := by
  have g0 := band_0062
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0063
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((55979921144 : ℝ) / 65536) ((55988782582 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_007_3 <;> assumption
