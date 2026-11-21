-- Prove2me | solution 1 for RH1E6S04.part_084_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T12:05:32.191553+00:00
-- url     : https://prove2.me/submissions/73cee8f3-126e-414f-a3a3-3e5fecc217a2

import Definitions.Def_RH1E6S04_D084_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0676 : RS5.BandZeros ((22918336034 : ℝ) / 65536) ((22923121889 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0676.s0 RH1E6S04_0676.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0676.s0 RH1E6S04_0676.rest = RH1E6S04_0676.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0676.s0 :: RH1E6S04_0676.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0676.s0.t = ((22918336034 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0676.s0]
  have e1 : RH1E6S04_0676.sL.t = ((22923121889 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0676.sL]
  rw [e0, e1] at h
  exact h

theorem band_0677 : RS5.BandZeros ((22923121889 : ℝ) / 65536) ((22927917074 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0677.s0 RH1E6S04_0677.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0677.s0 RH1E6S04_0677.rest = RH1E6S04_0677.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0677.s0 :: RH1E6S04_0677.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0677.s0.t = ((22923121889 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0677.s0]
  have e1 : RH1E6S04_0677.sL.t = ((22927917074 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0677.sL]
  rw [e0, e1] at h
  exact h

theorem part_084_2 : RS5.BandZeros ((22918336034 : ℝ) / 65536) ((22927917074 : ℝ) / 65536) 254 := by
  have g0 := band_0676
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0677
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((22918336034 : ℝ) / 65536) ((22927917074 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_084_2 <;> assumption
