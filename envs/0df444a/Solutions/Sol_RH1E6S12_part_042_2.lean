-- Prove2me | solution 1 for RH1E6S12.part_042_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T09:26:43.025072+00:00
-- url     : https://prove2.me/submissions/4fdc0710-b486-4823-8a46-ad5fa0620ae8

import Definitions.Def_RH1E6S12_D042_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0340 : RS5.BandZeros ((47403092495 : ℝ) / 65536) ((47407578818 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0340.s0 RH1E6S12_0340.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0340.s0 RH1E6S12_0340.rest = RH1E6S12_0340.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0340.s0 :: RH1E6S12_0340.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0340.s0.t = ((47403092495 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0340.s0]
  have e1 : RH1E6S12_0340.sL.t = ((47407578818 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0340.sL]
  rw [e0, e1] at h
  exact h

theorem band_0341 : RS5.BandZeros ((47407578818 : ℝ) / 65536) ((47412059806 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0341.s0 RH1E6S12_0341.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0341.s0 RH1E6S12_0341.rest = RH1E6S12_0341.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0341.s0 :: RH1E6S12_0341.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0341.s0.t = ((47407578818 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0341.s0]
  have e1 : RH1E6S12_0341.sL.t = ((47412059806 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0341.sL]
  rw [e0, e1] at h
  exact h

theorem part_042_2 : RS5.BandZeros ((47403092495 : ℝ) / 65536) ((47412059806 : ℝ) / 65536) 254 := by
  have g0 := band_0340
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0341
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((47403092495 : ℝ) / 65536) ((47412059806 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_042_2 <;> assumption
