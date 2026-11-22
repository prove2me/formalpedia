-- Prove2me | solution 1 for RH1E6S10.part_017_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T18:41:15.536172+00:00
-- url     : https://prove2.me/submissions/b364c448-fc3d-47c5-ac16-da9d75a26f47

import Definitions.Def_RH1E6S10_D017_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0136 : RS5.BandZeros ((39941428886 : ℝ) / 65536) ((39945992206 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0136.s0 RH1E6S10_0136.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0136.s0 RH1E6S10_0136.rest = RH1E6S10_0136.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0136.s0 :: RH1E6S10_0136.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0136.s0.t = ((39941428886 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0136.s0]
  have e1 : RH1E6S10_0136.sL.t = ((39945992206 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0136.sL]
  rw [e0, e1] at h
  exact h

theorem band_0137 : RS5.BandZeros ((39945992206 : ℝ) / 65536) ((39950546516 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0137.s0 RH1E6S10_0137.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0137.s0 RH1E6S10_0137.rest = RH1E6S10_0137.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0137.s0 :: RH1E6S10_0137.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0137.s0.t = ((39945992206 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0137.s0]
  have e1 : RH1E6S10_0137.sL.t = ((39950546516 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0137.sL]
  rw [e0, e1] at h
  exact h

theorem part_017_0 : RS5.BandZeros ((39941428886 : ℝ) / 65536) ((39950546516 : ℝ) / 65536) 254 := by
  have g0 := band_0136
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0137
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((39941428886 : ℝ) / 65536) ((39950546516 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_017_0 <;> assumption
