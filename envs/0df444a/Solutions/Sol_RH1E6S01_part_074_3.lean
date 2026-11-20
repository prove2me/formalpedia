-- Prove2me | solution 1 for RH1E6S01.part_074_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T01:56:13.590184+00:00
-- url     : https://prove2.me/submissions/84ae122e-3f07-4860-b868-1e75c1402197

import Definitions.Def_RH1E6S01_D074_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0598 : RS5.BandZeros ((12889711360 : ℝ) / 65536) ((12894773191 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0598.s0 RH1E6S01_0598.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0598.s0 RH1E6S01_0598.rest = RH1E6S01_0598.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0598.s0 :: RH1E6S01_0598.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0598.s0.t = ((12889711360 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0598.s0]
  have e1 : RH1E6S01_0598.sL.t = ((12894773191 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0598.sL]
  rw [e0, e1] at h
  exact h

theorem band_0599 : RS5.BandZeros ((12894773191 : ℝ) / 65536) ((12899814941 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0599.s0 RH1E6S01_0599.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0599.s0 RH1E6S01_0599.rest = RH1E6S01_0599.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0599.s0 :: RH1E6S01_0599.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0599.s0.t = ((12894773191 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0599.s0]
  have e1 : RH1E6S01_0599.sL.t = ((12899814941 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0599.sL]
  rw [e0, e1] at h
  exact h

theorem part_074_3 : RS5.BandZeros ((12889711360 : ℝ) / 65536) ((12899814941 : ℝ) / 65536) 254 := by
  have g0 := band_0598
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0599
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((12889711360 : ℝ) / 65536) ((12899814941 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_074_3 <;> assumption
