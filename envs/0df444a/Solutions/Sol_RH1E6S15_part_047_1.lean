-- Prove2me | solution 1 for RH1E6S15.part_047_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T10:38:31.790114+00:00
-- url     : https://prove2.me/submissions/b65a06be-9ce3-42ba-a6bd-8034c5838c25

import Definitions.Def_RH1E6S15_D047_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0378 : RS5.BandZeros ((57376546065 : ℝ) / 65536) ((57380968650 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0378.s0 RH1E6S15_0378.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0378.s0 RH1E6S15_0378.rest = RH1E6S15_0378.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0378.s0 :: RH1E6S15_0378.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0378.s0.t = ((57376546065 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0378.s0]
  have e1 : RH1E6S15_0378.sL.t = ((57380968650 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0378.sL]
  rw [e0, e1] at h
  exact h

theorem band_0379 : RS5.BandZeros ((57380968650 : ℝ) / 65536) ((57385369834 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0379.s0 RH1E6S15_0379.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0379.s0 RH1E6S15_0379.rest = RH1E6S15_0379.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0379.s0 :: RH1E6S15_0379.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0379.s0.t = ((57380968650 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0379.s0]
  have e1 : RH1E6S15_0379.sL.t = ((57385369834 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0379.sL]
  rw [e0, e1] at h
  exact h

theorem part_047_1 : RS5.BandZeros ((57376546065 : ℝ) / 65536) ((57385369834 : ℝ) / 65536) 254 := by
  have g0 := band_0378
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0379
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((57376546065 : ℝ) / 65536) ((57385369834 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_047_1 <;> assumption
