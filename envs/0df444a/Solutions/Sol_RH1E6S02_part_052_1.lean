-- Prove2me | solution 1 for RH1E6S02.part_052_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T03:58:54.400771+00:00
-- url     : https://prove2.me/submissions/20779f1a-e7ae-4b93-94c2-2c904d6c2dc5

import Definitions.Def_RH1E6S02_D052_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0418 : RS5.BandZeros ((15200198244 : ℝ) / 65536) ((15205198102 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0418.s0 RH1E6S02_0418.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0418.s0 RH1E6S02_0418.rest = RH1E6S02_0418.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0418.s0 :: RH1E6S02_0418.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0418.s0.t = ((15200198244 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0418.s0]
  have e1 : RH1E6S02_0418.sL.t = ((15205198102 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0418.sL]
  rw [e0, e1] at h
  exact h

theorem band_0419 : RS5.BandZeros ((15205198102 : ℝ) / 65536) ((15210155498 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0419.s0 RH1E6S02_0419.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0419.s0 RH1E6S02_0419.rest = RH1E6S02_0419.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0419.s0 :: RH1E6S02_0419.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0419.s0.t = ((15205198102 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0419.s0]
  have e1 : RH1E6S02_0419.sL.t = ((15210155498 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0419.sL]
  rw [e0, e1] at h
  exact h

theorem part_052_1 : RS5.BandZeros ((15200198244 : ℝ) / 65536) ((15210155498 : ℝ) / 65536) 254 := by
  have g0 := band_0418
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0419
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((15200198244 : ℝ) / 65536) ((15210155498 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_052_1 <;> assumption
