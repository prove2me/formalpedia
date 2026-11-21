-- Prove2me | solution 1 for RH1E6S06.part_063_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T20:59:45.537476+00:00
-- url     : https://prove2.me/submissions/386cdf79-2aa8-4292-a0e3-ccb900c8ece2

import Definitions.Def_RH1E6S06_D063_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0510 : RS5.BandZeros ((28615916214 : ℝ) / 65536) ((28620592799 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0510.s0 RH1E6S06_0510.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0510.s0 RH1E6S06_0510.rest = RH1E6S06_0510.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0510.s0 :: RH1E6S06_0510.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0510.s0.t = ((28615916214 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0510.s0]
  have e1 : RH1E6S06_0510.sL.t = ((28620592799 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0510.sL]
  rw [e0, e1] at h
  exact h

theorem band_0511 : RS5.BandZeros ((28620592799 : ℝ) / 65536) ((28625300689 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0511.s0 RH1E6S06_0511.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0511.s0 RH1E6S06_0511.rest = RH1E6S06_0511.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0511.s0 :: RH1E6S06_0511.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0511.s0.t = ((28620592799 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0511.s0]
  have e1 : RH1E6S06_0511.sL.t = ((28625300689 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0511.sL]
  rw [e0, e1] at h
  exact h

theorem part_063_3 : RS5.BandZeros ((28615916214 : ℝ) / 65536) ((28625300689 : ℝ) / 65536) 254 := by
  have g0 := band_0510
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0511
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((28615916214 : ℝ) / 65536) ((28625300689 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_063_3 <;> assumption
