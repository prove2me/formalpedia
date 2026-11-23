-- Prove2me | solution 1 for RH1E6S14.part_027_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T04:04:53.475417+00:00
-- url     : https://prove2.me/submissions/07497de4-da8e-4d6f-b9e6-0086b284fa21

import Definitions.Def_RH1E6S14_D027_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0222 : RS5.BandZeros ((53415684454 : ℝ) / 65536) ((53420117620 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0222.s0 RH1E6S14_0222.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0222.s0 RH1E6S14_0222.rest = RH1E6S14_0222.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0222.s0 :: RH1E6S14_0222.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0222.s0.t = ((53415684454 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0222.s0]
  have e1 : RH1E6S14_0222.sL.t = ((53420117620 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0222.sL]
  rw [e0, e1] at h
  exact h

theorem band_0223 : RS5.BandZeros ((53420117620 : ℝ) / 65536) ((53424576598 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0223.s0 RH1E6S14_0223.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0223.s0 RH1E6S14_0223.rest = RH1E6S14_0223.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0223.s0 :: RH1E6S14_0223.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0223.s0.t = ((53420117620 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0223.s0]
  have e1 : RH1E6S14_0223.sL.t = ((53424576598 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0223.sL]
  rw [e0, e1] at h
  exact h

theorem part_027_3 : RS5.BandZeros ((53415684454 : ℝ) / 65536) ((53424576598 : ℝ) / 65536) 254 := by
  have g0 := band_0222
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0223
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((53415684454 : ℝ) / 65536) ((53424576598 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_027_3 <;> assumption
