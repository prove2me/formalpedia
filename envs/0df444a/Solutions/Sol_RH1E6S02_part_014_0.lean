-- Prove2me | solution 1 for RH1E6S02.part_014_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T02:36:58.738011+00:00
-- url     : https://prove2.me/submissions/be9514d2-a8d6-4f5c-a3dc-a31ee71b3f0a

import Definitions.Def_RH1E6S02_D014_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0112 : RS5.BandZeros ((13670963744 : ℝ) / 65536) ((13675992979 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0112.s0 RH1E6S02_0112.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0112.s0 RH1E6S02_0112.rest = RH1E6S02_0112.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0112.s0 :: RH1E6S02_0112.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0112.s0.t = ((13670963744 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0112.s0]
  have e1 : RH1E6S02_0112.sL.t = ((13675992979 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0112.sL]
  rw [e0, e1] at h
  exact h

theorem band_0113 : RS5.BandZeros ((13675992979 : ℝ) / 65536) ((13681000352 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0113.s0 RH1E6S02_0113.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0113.s0 RH1E6S02_0113.rest = RH1E6S02_0113.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0113.s0 :: RH1E6S02_0113.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0113.s0.t = ((13675992979 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0113.s0]
  have e1 : RH1E6S02_0113.sL.t = ((13681000352 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0113.sL]
  rw [e0, e1] at h
  exact h

theorem part_014_0 : RS5.BandZeros ((13670963744 : ℝ) / 65536) ((13681000352 : ℝ) / 65536) 254 := by
  have g0 := band_0112
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0113
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((13670963744 : ℝ) / 65536) ((13681000352 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_014_0 <;> assumption
