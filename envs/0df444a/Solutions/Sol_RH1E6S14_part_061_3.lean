-- Prove2me | solution 1 for RH1E6S14.part_061_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T05:59:07.742658+00:00
-- url     : https://prove2.me/submissions/a891044a-6bba-41fe-86f7-89325ce73ed5

import Definitions.Def_RH1E6S14_D061_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0494 : RS5.BandZeros ((54622745784 : ℝ) / 65536) ((54627163187 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0494.s0 RH1E6S14_0494.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0494.s0 RH1E6S14_0494.rest = RH1E6S14_0494.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0494.s0 :: RH1E6S14_0494.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0494.s0.t = ((54622745784 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0494.s0]
  have e1 : RH1E6S14_0494.sL.t = ((54627163187 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0494.sL]
  rw [e0, e1] at h
  exact h

theorem band_0495 : RS5.BandZeros ((54627163187 : ℝ) / 65536) ((54631605379 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0495.s0 RH1E6S14_0495.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0495.s0 RH1E6S14_0495.rest = RH1E6S14_0495.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0495.s0 :: RH1E6S14_0495.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0495.s0.t = ((54627163187 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0495.s0]
  have e1 : RH1E6S14_0495.sL.t = ((54631605379 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0495.sL]
  rw [e0, e1] at h
  exact h

theorem part_061_3 : RS5.BandZeros ((54622745784 : ℝ) / 65536) ((54631605379 : ℝ) / 65536) 254 := by
  have g0 := band_0494
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0495
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((54622745784 : ℝ) / 65536) ((54631605379 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_061_3 <;> assumption
