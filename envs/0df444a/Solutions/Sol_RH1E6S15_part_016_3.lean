-- Prove2me | solution 1 for RH1E6S15.part_016_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T08:46:03.4174+00:00
-- url     : https://prove2.me/submissions/32d79499-9de4-44cb-b797-10451d0a1d72

import Definitions.Def_RH1E6S15_D016_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0134 : RS5.BandZeros ((56298406575 : ℝ) / 65536) ((56302829480 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0134.s0 RH1E6S15_0134.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0134.s0 RH1E6S15_0134.rest = RH1E6S15_0134.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0134.s0 :: RH1E6S15_0134.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0134.s0.t = ((56298406575 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0134.s0]
  have e1 : RH1E6S15_0134.sL.t = ((56302829480 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0134.sL]
  rw [e0, e1] at h
  exact h

theorem band_0135 : RS5.BandZeros ((56302829480 : ℝ) / 65536) ((56307247615 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0135.s0 RH1E6S15_0135.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0135.s0 RH1E6S15_0135.rest = RH1E6S15_0135.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0135.s0 :: RH1E6S15_0135.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0135.s0.t = ((56302829480 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0135.s0]
  have e1 : RH1E6S15_0135.sL.t = ((56307247615 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0135.sL]
  rw [e0, e1] at h
  exact h

theorem part_016_3 : RS5.BandZeros ((56298406575 : ℝ) / 65536) ((56307247615 : ℝ) / 65536) 254 := by
  have g0 := band_0134
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0135
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((56298406575 : ℝ) / 65536) ((56307247615 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_016_3 <;> assumption
