-- Prove2me | solution 1 for RH1E6S05.part_059_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T15:41:12.767396+00:00
-- url     : https://prove2.me/submissions/28a7cc5c-6028-4110-96a1-667e63db23de

import Definitions.Def_RH1E6S05_D059_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0478 : RS5.BandZeros ((25215056785 : ℝ) / 65536) ((25219810518 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0478.s0 RH1E6S05_0478.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0478.s0 RH1E6S05_0478.rest = RH1E6S05_0478.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0478.s0 :: RH1E6S05_0478.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0478.s0.t = ((25215056785 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0478.s0]
  have e1 : RH1E6S05_0478.sL.t = ((25219810518 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0478.sL]
  rw [e0, e1] at h
  exact h

theorem band_0479 : RS5.BandZeros ((25219810518 : ℝ) / 65536) ((25224545491 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0479.s0 RH1E6S05_0479.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0479.s0 RH1E6S05_0479.rest = RH1E6S05_0479.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0479.s0 :: RH1E6S05_0479.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0479.s0.t = ((25219810518 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0479.s0]
  have e1 : RH1E6S05_0479.sL.t = ((25224545491 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0479.sL]
  rw [e0, e1] at h
  exact h

theorem part_059_3 : RS5.BandZeros ((25215056785 : ℝ) / 65536) ((25224545491 : ℝ) / 65536) 254 := by
  have g0 := band_0478
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0479
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((25215056785 : ℝ) / 65536) ((25224545491 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_059_3 <;> assumption
