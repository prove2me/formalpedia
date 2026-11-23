-- Prove2me | solution 1 for RH1E6S13.part_056_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T23:57:46.902358+00:00
-- url     : https://prove2.me/submissions/99ec4e7e-24d3-47d4-a1de-069d9280c50e

import Definitions.Def_RH1E6S13_D056_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0448 : RS5.BandZeros ((51152721309 : ℝ) / 65536) ((51157162058 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0448.s0 RH1E6S13_0448.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0448.s0 RH1E6S13_0448.rest = RH1E6S13_0448.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0448.s0 :: RH1E6S13_0448.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0448.s0.t = ((51152721309 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0448.s0]
  have e1 : RH1E6S13_0448.sL.t = ((51157162058 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0448.sL]
  rw [e0, e1] at h
  exact h

theorem band_0449 : RS5.BandZeros ((51157162058 : ℝ) / 65536) ((51161637879 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0449.s0 RH1E6S13_0449.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0449.s0 RH1E6S13_0449.rest = RH1E6S13_0449.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0449.s0 :: RH1E6S13_0449.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0449.s0.t = ((51157162058 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0449.s0]
  have e1 : RH1E6S13_0449.sL.t = ((51161637879 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0449.sL]
  rw [e0, e1] at h
  exact h

theorem part_056_0 : RS5.BandZeros ((51152721309 : ℝ) / 65536) ((51161637879 : ℝ) / 65536) 254 := by
  have g0 := band_0448
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0449
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((51152721309 : ℝ) / 65536) ((51161637879 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_056_0 <;> assumption
