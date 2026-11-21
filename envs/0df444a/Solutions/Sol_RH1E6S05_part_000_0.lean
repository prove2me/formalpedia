-- Prove2me | solution 1 for RH1E6S05.part_000_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T12:05:38.216506+00:00
-- url     : https://prove2.me/submissions/1886a253-829a-479e-bb43-5d5a6a4d26aa

import Definitions.Def_RH1E6S05_D000_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0000 : RS5.BandZeros ((22937600000 : ℝ) / 65536) ((22942396279 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0000.s0 RH1E6S05_0000.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0000.s0 RH1E6S05_0000.rest = RH1E6S05_0000.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0000.s0 :: RH1E6S05_0000.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0000.s0.t = ((22937600000 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0000.s0]
  have e1 : RH1E6S05_0000.sL.t = ((22942396279 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0000.sL]
  rw [e0, e1] at h
  exact h

theorem band_0001 : RS5.BandZeros ((22942396279 : ℝ) / 65536) ((22947172255 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0001.s0 RH1E6S05_0001.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0001.s0 RH1E6S05_0001.rest = RH1E6S05_0001.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0001.s0 :: RH1E6S05_0001.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0001.s0.t = ((22942396279 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0001.s0]
  have e1 : RH1E6S05_0001.sL.t = ((22947172255 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0001.sL]
  rw [e0, e1] at h
  exact h

theorem part_000_0 : RS5.BandZeros ((22937600000 : ℝ) / 65536) ((22947172255 : ℝ) / 65536) 254 := by
  have g0 := band_0000
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0001
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((22937600000 : ℝ) / 65536) ((22947172255 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_000_0 <;> assumption
