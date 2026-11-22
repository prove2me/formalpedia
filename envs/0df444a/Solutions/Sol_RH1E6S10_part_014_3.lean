-- Prove2me | solution 1 for RH1E6S10.part_014_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T18:26:07.981456+00:00
-- url     : https://prove2.me/submissions/1b0e3992-1452-40bd-8e6d-059173750092

import Definitions.Def_RH1E6S10_D014_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0118 : RS5.BandZeros ((39859460690 : ℝ) / 65536) ((39863988959 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0118.s0 RH1E6S10_0118.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0118.s0 RH1E6S10_0118.rest = RH1E6S10_0118.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0118.s0 :: RH1E6S10_0118.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0118.s0.t = ((39859460690 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0118.s0]
  have e1 : RH1E6S10_0118.sL.t = ((39863988959 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0118.sL]
  rw [e0, e1] at h
  exact h

theorem band_0119 : RS5.BandZeros ((39863988959 : ℝ) / 65536) ((39868562018 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0119.s0 RH1E6S10_0119.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0119.s0 RH1E6S10_0119.rest = RH1E6S10_0119.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0119.s0 :: RH1E6S10_0119.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0119.s0.t = ((39863988959 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0119.s0]
  have e1 : RH1E6S10_0119.sL.t = ((39868562018 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0119.sL]
  rw [e0, e1] at h
  exact h

theorem part_014_3 : RS5.BandZeros ((39859460690 : ℝ) / 65536) ((39868562018 : ℝ) / 65536) 254 := by
  have g0 := band_0118
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0119
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((39859460690 : ℝ) / 65536) ((39868562018 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_014_3 <;> assumption
