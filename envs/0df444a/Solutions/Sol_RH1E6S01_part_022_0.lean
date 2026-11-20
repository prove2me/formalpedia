-- Prove2me | solution 1 for RH1E6S01.part_022_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T00:05:41.44296+00:00
-- url     : https://prove2.me/submissions/c16372ad-3680-451b-a47d-ff0ad94df1c9

import Definitions.Def_RH1E6S01_D022_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0176 : RS5.BandZeros ((10739384713 : ℝ) / 65536) ((10744537369 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0176.s0 RH1E6S01_0176.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0176.s0 RH1E6S01_0176.rest = RH1E6S01_0176.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0176.s0 :: RH1E6S01_0176.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0176.s0.t = ((10739384713 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0176.s0]
  have e1 : RH1E6S01_0176.sL.t = ((10744537369 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0176.sL]
  rw [e0, e1] at h
  exact h

theorem band_0177 : RS5.BandZeros ((10744537369 : ℝ) / 65536) ((10749689782 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0177.s0 RH1E6S01_0177.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0177.s0 RH1E6S01_0177.rest = RH1E6S01_0177.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0177.s0 :: RH1E6S01_0177.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0177.s0.t = ((10744537369 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0177.s0]
  have e1 : RH1E6S01_0177.sL.t = ((10749689782 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0177.sL]
  rw [e0, e1] at h
  exact h

theorem part_022_0 : RS5.BandZeros ((10739384713 : ℝ) / 65536) ((10749689782 : ℝ) / 65536) 254 := by
  have g0 := band_0176
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0177
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((10739384713 : ℝ) / 65536) ((10749689782 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_022_0 <;> assumption
