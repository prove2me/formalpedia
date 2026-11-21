-- Prove2me | solution 1 for RH1E6S05.part_037_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T13:54:00.238226+00:00
-- url     : https://prove2.me/submissions/9c5e3c55-8197-4598-b0b6-cd8f59642999

import Definitions.Def_RH1E6S05_D037_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0296 : RS5.BandZeros ((24350227338 : ℝ) / 65536) ((24354986799 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0296.s0 RH1E6S05_0296.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0296.s0 RH1E6S05_0296.rest = RH1E6S05_0296.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0296.s0 :: RH1E6S05_0296.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0296.s0.t = ((24350227338 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0296.s0]
  have e1 : RH1E6S05_0296.sL.t = ((24354986799 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0296.sL]
  rw [e0, e1] at h
  exact h

theorem band_0297 : RS5.BandZeros ((24354986799 : ℝ) / 65536) ((24359746176 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0297.s0 RH1E6S05_0297.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0297.s0 RH1E6S05_0297.rest = RH1E6S05_0297.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0297.s0 :: RH1E6S05_0297.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0297.s0.t = ((24354986799 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0297.s0]
  have e1 : RH1E6S05_0297.sL.t = ((24359746176 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0297.sL]
  rw [e0, e1] at h
  exact h

theorem part_037_0 : RS5.BandZeros ((24350227338 : ℝ) / 65536) ((24359746176 : ℝ) / 65536) 254 := by
  have g0 := band_0296
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0297
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((24350227338 : ℝ) / 65536) ((24359746176 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_037_0 <;> assumption
