-- Prove2me | solution 1 for RH1E6S15.part_060_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T11:33:58.911854+00:00
-- url     : https://prove2.me/submissions/fde5adcc-89ed-48c9-9309-3f75142588a8

import Definitions.Def_RH1E6S15_D060_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0486 : RS5.BandZeros ((57853213288 : ℝ) / 65536) ((57857611071 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0486.s0 RH1E6S15_0486.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0486.s0 RH1E6S15_0486.rest = RH1E6S15_0486.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0486.s0 :: RH1E6S15_0486.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0486.s0.t = ((57853213288 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0486.s0]
  have e1 : RH1E6S15_0486.sL.t = ((57857611071 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0486.sL]
  rw [e0, e1] at h
  exact h

theorem band_0487 : RS5.BandZeros ((57857611071 : ℝ) / 65536) ((57862045175 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0487.s0 RH1E6S15_0487.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0487.s0 RH1E6S15_0487.rest = RH1E6S15_0487.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0487.s0 :: RH1E6S15_0487.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0487.s0.t = ((57857611071 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0487.s0]
  have e1 : RH1E6S15_0487.sL.t = ((57862045175 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0487.sL]
  rw [e0, e1] at h
  exact h

theorem part_060_3 : RS5.BandZeros ((57853213288 : ℝ) / 65536) ((57862045175 : ℝ) / 65536) 254 := by
  have g0 := band_0486
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0487
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((57853213288 : ℝ) / 65536) ((57862045175 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_060_3 <;> assumption
