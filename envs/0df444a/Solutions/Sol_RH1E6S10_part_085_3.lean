-- Prove2me | solution 1 for RH1E6S10.part_085_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T02:49:44.46296+00:00
-- url     : https://prove2.me/submissions/ea4684c8-f601-4c6d-97fe-5ca30e1c9017

import Definitions.Def_RH1E6S10_D085_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0686 : RS5.BandZeros ((42439678806 : ℝ) / 65536) ((42444209225 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0686.s0 RH1E6S10_0686.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0686.s0 RH1E6S10_0686.rest = RH1E6S10_0686.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0686.s0 :: RH1E6S10_0686.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0686.s0.t = ((42439678806 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0686.s0]
  have e1 : RH1E6S10_0686.sL.t = ((42444209225 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0686.sL]
  rw [e0, e1] at h
  exact h

theorem band_0687 : RS5.BandZeros ((42444209225 : ℝ) / 65536) ((42448739603 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0687.s0 RH1E6S10_0687.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0687.s0 RH1E6S10_0687.rest = RH1E6S10_0687.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0687.s0 :: RH1E6S10_0687.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0687.s0.t = ((42444209225 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0687.s0]
  have e1 : RH1E6S10_0687.sL.t = ((42448739603 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0687.sL]
  rw [e0, e1] at h
  exact h

theorem part_085_3 : RS5.BandZeros ((42439678806 : ℝ) / 65536) ((42448739603 : ℝ) / 65536) 254 := by
  have g0 := band_0686
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0687
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((42439678806 : ℝ) / 65536) ((42448739603 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_085_3 <;> assumption
