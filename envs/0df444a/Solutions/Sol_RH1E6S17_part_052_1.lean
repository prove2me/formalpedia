-- Prove2me | solution 1 for RH1E6S17.part_052_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T22:32:14.666585+00:00
-- url     : https://prove2.me/submissions/00b0c5a3-b75e-4ed4-b38d-6e0751198d18

import Definitions.Def_RH1E6S17_D052_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0418 : RS5.BandZeros ((64089852063 : ℝ) / 65536) ((64094200456 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0418.s0 RH1E6S17_0418.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0418.s0 RH1E6S17_0418.rest = RH1E6S17_0418.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0418.s0 :: RH1E6S17_0418.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0418.s0.t = ((64089852063 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0418.s0]
  have e1 : RH1E6S17_0418.sL.t = ((64094200456 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0418.sL]
  rw [e0, e1] at h
  exact h

theorem band_0419 : RS5.BandZeros ((64094200456 : ℝ) / 65536) ((64098591877 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0419.s0 RH1E6S17_0419.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0419.s0 RH1E6S17_0419.rest = RH1E6S17_0419.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0419.s0 :: RH1E6S17_0419.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0419.s0.t = ((64094200456 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0419.s0]
  have e1 : RH1E6S17_0419.sL.t = ((64098591877 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0419.sL]
  rw [e0, e1] at h
  exact h

theorem part_052_1 : RS5.BandZeros ((64089852063 : ℝ) / 65536) ((64098591877 : ℝ) / 65536) 254 := by
  have g0 := band_0418
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0419
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((64089852063 : ℝ) / 65536) ((64098591877 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_052_1 <;> assumption
