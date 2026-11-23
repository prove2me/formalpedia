-- Prove2me | solution 1 for RH1E6S14.part_022_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T03:46:54.438861+00:00
-- url     : https://prove2.me/submissions/8e7dede3-7690-4d66-9384-04de09ffdfe8

import Definitions.Def_RH1E6S14_D022_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0178 : RS5.BandZeros ((53220218059 : ℝ) / 65536) ((53224635113 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0178.s0 RH1E6S14_0178.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0178.s0 RH1E6S14_0178.rest = RH1E6S14_0178.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0178.s0 :: RH1E6S14_0178.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0178.s0.t = ((53220218059 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0178.s0]
  have e1 : RH1E6S14_0178.sL.t = ((53224635113 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0178.sL]
  rw [e0, e1] at h
  exact h

theorem band_0179 : RS5.BandZeros ((53224635113 : ℝ) / 65536) ((53229087445 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0179.s0 RH1E6S14_0179.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0179.s0 RH1E6S14_0179.rest = RH1E6S14_0179.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0179.s0 :: RH1E6S14_0179.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0179.s0.t = ((53224635113 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0179.s0]
  have e1 : RH1E6S14_0179.sL.t = ((53229087445 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0179.sL]
  rw [e0, e1] at h
  exact h

theorem part_022_1 : RS5.BandZeros ((53220218059 : ℝ) / 65536) ((53229087445 : ℝ) / 65536) 254 := by
  have g0 := band_0178
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0179
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((53220218059 : ℝ) / 65536) ((53229087445 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_022_1 <;> assumption
