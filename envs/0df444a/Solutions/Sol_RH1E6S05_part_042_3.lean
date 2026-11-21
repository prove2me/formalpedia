-- Prove2me | solution 1 for RH1E6S05.part_042_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T14:06:44.899947+00:00
-- url     : https://prove2.me/submissions/9d49ee05-d65f-419b-aa18-821f9a731165

import Definitions.Def_RH1E6S05_D042_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0342 : RS5.BandZeros ((24569075267 : ℝ) / 65536) ((24573812134 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0342.s0 RH1E6S05_0342.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0342.s0 RH1E6S05_0342.rest = RH1E6S05_0342.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0342.s0 :: RH1E6S05_0342.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0342.s0.t = ((24569075267 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0342.s0]
  have e1 : RH1E6S05_0342.sL.t = ((24573812134 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0342.sL]
  rw [e0, e1] at h
  exact h

theorem band_0343 : RS5.BandZeros ((24573812134 : ℝ) / 65536) ((24578577001 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0343.s0 RH1E6S05_0343.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0343.s0 RH1E6S05_0343.rest = RH1E6S05_0343.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0343.s0 :: RH1E6S05_0343.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0343.s0.t = ((24573812134 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0343.s0]
  have e1 : RH1E6S05_0343.sL.t = ((24578577001 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0343.sL]
  rw [e0, e1] at h
  exact h

theorem part_042_3 : RS5.BandZeros ((24569075267 : ℝ) / 65536) ((24578577001 : ℝ) / 65536) 254 := by
  have g0 := band_0342
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0343
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((24569075267 : ℝ) / 65536) ((24578577001 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_042_3 <;> assumption
