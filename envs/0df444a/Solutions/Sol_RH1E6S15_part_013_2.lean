-- Prove2me | solution 1 for RH1E6S15.part_013_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T08:39:49.010388+00:00
-- url     : https://prove2.me/submissions/e92b3467-e767-47b1-9eeb-3e3c404c1315

import Definitions.Def_RH1E6S15_D013_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0108 : RS5.BandZeros ((56183419662 : ℝ) / 65536) ((56187828154 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0108.s0 RH1E6S15_0108.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0108.s0 RH1E6S15_0108.rest = RH1E6S15_0108.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0108.s0 :: RH1E6S15_0108.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0108.s0.t = ((56183419662 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0108.s0]
  have e1 : RH1E6S15_0108.sL.t = ((56187828154 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0108.sL]
  rw [e0, e1] at h
  exact h

theorem band_0109 : RS5.BandZeros ((56187828154 : ℝ) / 65536) ((56192265609 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0109.s0 RH1E6S15_0109.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0109.s0 RH1E6S15_0109.rest = RH1E6S15_0109.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0109.s0 :: RH1E6S15_0109.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0109.s0.t = ((56187828154 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0109.s0]
  have e1 : RH1E6S15_0109.sL.t = ((56192265609 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0109.sL]
  rw [e0, e1] at h
  exact h

theorem part_013_2 : RS5.BandZeros ((56183419662 : ℝ) / 65536) ((56192265609 : ℝ) / 65536) 254 := by
  have g0 := band_0108
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0109
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((56183419662 : ℝ) / 65536) ((56192265609 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_013_2 <;> assumption
