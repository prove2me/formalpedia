-- Prove2me | solution 1 for RH1E6S15.part_004_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T07:58:59.468369+00:00
-- url     : https://prove2.me/submissions/a49a72a8-b133-4ea4-ac99-180acb107813

import Definitions.Def_RH1E6S15_D004_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0036 : RS5.BandZeros ((55864896420 : ℝ) / 65536) ((55869304938 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0036.s0 RH1E6S15_0036.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0036.s0 RH1E6S15_0036.rest = RH1E6S15_0036.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0036.s0 :: RH1E6S15_0036.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0036.s0.t = ((55864896420 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0036.s0]
  have e1 : RH1E6S15_0036.sL.t = ((55869304938 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0036.sL]
  rw [e0, e1] at h
  exact h

theorem band_0037 : RS5.BandZeros ((55869304938 : ℝ) / 65536) ((55873734936 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0037.s0 RH1E6S15_0037.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0037.s0 RH1E6S15_0037.rest = RH1E6S15_0037.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0037.s0 :: RH1E6S15_0037.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0037.s0.t = ((55869304938 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0037.s0]
  have e1 : RH1E6S15_0037.sL.t = ((55873734936 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0037.sL]
  rw [e0, e1] at h
  exact h

theorem part_004_2 : RS5.BandZeros ((55864896420 : ℝ) / 65536) ((55873734936 : ℝ) / 65536) 254 := by
  have g0 := band_0036
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0037
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((55864896420 : ℝ) / 65536) ((55873734936 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_004_2 <;> assumption
