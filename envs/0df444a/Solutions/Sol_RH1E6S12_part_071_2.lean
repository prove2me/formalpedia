-- Prove2me | solution 1 for RH1E6S12.part_071_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T16:47:13.462921+00:00
-- url     : https://prove2.me/submissions/322a4d8f-118c-4203-8a4d-ea186108cc9b

import Definitions.Def_RH1E6S12_D071_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0572 : RS5.BandZeros ((48443224682 : ℝ) / 65536) ((48447670511 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0572.s0 RH1E6S12_0572.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0572.s0 RH1E6S12_0572.rest = RH1E6S12_0572.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0572.s0 :: RH1E6S12_0572.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0572.s0.t = ((48443224682 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0572.s0]
  have e1 : RH1E6S12_0572.sL.t = ((48447670511 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0572.sL]
  rw [e0, e1] at h
  exact h

theorem band_0573 : RS5.BandZeros ((48447670511 : ℝ) / 65536) ((48452165177 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0573.s0 RH1E6S12_0573.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0573.s0 RH1E6S12_0573.rest = RH1E6S12_0573.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0573.s0 :: RH1E6S12_0573.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0573.s0.t = ((48447670511 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0573.s0]
  have e1 : RH1E6S12_0573.sL.t = ((48452165177 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0573.sL]
  rw [e0, e1] at h
  exact h

theorem part_071_2 : RS5.BandZeros ((48443224682 : ℝ) / 65536) ((48452165177 : ℝ) / 65536) 254 := by
  have g0 := band_0572
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0573
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((48443224682 : ℝ) / 65536) ((48452165177 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_071_2 <;> assumption
