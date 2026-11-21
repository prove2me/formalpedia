-- Prove2me | solution 1 for RH1E6S07.part_052_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T01:22:20.180074+00:00
-- url     : https://prove2.me/submissions/72c3ffe2-5a59-469a-996d-8ba7688b1842

import Definitions.Def_RH1E6S07_D052_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0418 : RS5.BandZeros ((31440953976 : ℝ) / 65536) ((31445585464 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0418.s0 RH1E6S07_0418.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0418.s0 RH1E6S07_0418.rest = RH1E6S07_0418.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0418.s0 :: RH1E6S07_0418.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0418.s0.t = ((31440953976 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0418.s0]
  have e1 : RH1E6S07_0418.sL.t = ((31445585464 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0418.sL]
  rw [e0, e1] at h
  exact h

theorem band_0419 : RS5.BandZeros ((31445585464 : ℝ) / 65536) ((31450237930 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0419.s0 RH1E6S07_0419.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0419.s0 RH1E6S07_0419.rest = RH1E6S07_0419.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0419.s0 :: RH1E6S07_0419.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0419.s0.t = ((31445585464 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0419.s0]
  have e1 : RH1E6S07_0419.sL.t = ((31450237930 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0419.sL]
  rw [e0, e1] at h
  exact h

theorem part_052_1 : RS5.BandZeros ((31440953976 : ℝ) / 65536) ((31450237930 : ℝ) / 65536) 254 := by
  have g0 := band_0418
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0419
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((31440953976 : ℝ) / 65536) ((31450237930 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_052_1 <;> assumption
