-- Prove2me | solution 1 for RH1E6S05.part_046_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T14:16:46.048876+00:00
-- url     : https://prove2.me/submissions/a866376e-d3e9-486b-b6ad-f694bbcb7dea

import Definitions.Def_RH1E6S05_D046_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0368 : RS5.BandZeros ((24692674727 : ℝ) / 65536) ((24697418790 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0368.s0 RH1E6S05_0368.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0368.s0 RH1E6S05_0368.rest = RH1E6S05_0368.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0368.s0 :: RH1E6S05_0368.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0368.s0.t = ((24692674727 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0368.s0]
  have e1 : RH1E6S05_0368.sL.t = ((24697418790 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0368.sL]
  rw [e0, e1] at h
  exact h

theorem band_0369 : RS5.BandZeros ((24697418790 : ℝ) / 65536) ((24702190841 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0369.s0 RH1E6S05_0369.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0369.s0 RH1E6S05_0369.rest = RH1E6S05_0369.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0369.s0 :: RH1E6S05_0369.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0369.s0.t = ((24697418790 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0369.s0]
  have e1 : RH1E6S05_0369.sL.t = ((24702190841 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0369.sL]
  rw [e0, e1] at h
  exact h

theorem part_046_0 : RS5.BandZeros ((24692674727 : ℝ) / 65536) ((24702190841 : ℝ) / 65536) 254 := by
  have g0 := band_0368
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0369
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((24692674727 : ℝ) / 65536) ((24702190841 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_046_0 <;> assumption
