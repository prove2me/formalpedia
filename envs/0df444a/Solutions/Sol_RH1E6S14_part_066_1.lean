-- Prove2me | solution 1 for RH1E6S14.part_066_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T06:16:36.970809+00:00
-- url     : https://prove2.me/submissions/6352bac2-3a8e-45b1-b41f-be86a2561d5b

import Definitions.Def_RH1E6S14_D066_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0530 : RS5.BandZeros ((54782303646 : ℝ) / 65536) ((54786755313 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0530.s0 RH1E6S14_0530.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0530.s0 RH1E6S14_0530.rest = RH1E6S14_0530.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0530.s0 :: RH1E6S14_0530.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0530.s0.t = ((54782303646 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0530.s0]
  have e1 : RH1E6S14_0530.sL.t = ((54786755313 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0530.sL]
  rw [e0, e1] at h
  exact h

theorem band_0531 : RS5.BandZeros ((54786755313 : ℝ) / 65536) ((54791178713 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0531.s0 RH1E6S14_0531.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0531.s0 RH1E6S14_0531.rest = RH1E6S14_0531.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0531.s0 :: RH1E6S14_0531.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0531.s0.t = ((54786755313 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0531.s0]
  have e1 : RH1E6S14_0531.sL.t = ((54791178713 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0531.sL]
  rw [e0, e1] at h
  exact h

theorem part_066_1 : RS5.BandZeros ((54782303646 : ℝ) / 65536) ((54791178713 : ℝ) / 65536) 254 := by
  have g0 := band_0530
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0531
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((54782303646 : ℝ) / 65536) ((54791178713 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_066_1 <;> assumption
