-- Prove2me | solution 1 for RH1E6S02.part_046_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T03:46:41.998333+00:00
-- url     : https://prove2.me/submissions/2d7cfd50-f044-4fb2-98a5-6ce3df59cd16

import Definitions.Def_RH1E6S02_D046_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0368 : RS5.BandZeros ((14951375148 : ℝ) / 65536) ((14956356684 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0368.s0 RH1E6S02_0368.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0368.s0 RH1E6S02_0368.rest = RH1E6S02_0368.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0368.s0 :: RH1E6S02_0368.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0368.s0.t = ((14951375148 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0368.s0]
  have e1 : RH1E6S02_0368.sL.t = ((14956356684 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0368.sL]
  rw [e0, e1] at h
  exact h

theorem band_0369 : RS5.BandZeros ((14956356684 : ℝ) / 65536) ((14961331313 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0369.s0 RH1E6S02_0369.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0369.s0 RH1E6S02_0369.rest = RH1E6S02_0369.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0369.s0 :: RH1E6S02_0369.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0369.s0.t = ((14956356684 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0369.s0]
  have e1 : RH1E6S02_0369.sL.t = ((14961331313 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0369.sL]
  rw [e0, e1] at h
  exact h

theorem part_046_0 : RS5.BandZeros ((14951375148 : ℝ) / 65536) ((14961331313 : ℝ) / 65536) 254 := by
  have g0 := band_0368
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0369
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((14951375148 : ℝ) / 65536) ((14961331313 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_046_0 <;> assumption
