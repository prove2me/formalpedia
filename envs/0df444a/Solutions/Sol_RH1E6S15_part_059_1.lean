-- Prove2me | solution 1 for RH1E6S15.part_059_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T11:28:10.145865+00:00
-- url     : https://prove2.me/submissions/319e9d67-aed3-4869-92a7-f25ac2bf909c

import Definitions.Def_RH1E6S15_D059_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0474 : RS5.BandZeros ((57800266243 : ℝ) / 65536) ((57804669902 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0474.s0 RH1E6S15_0474.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0474.s0 RH1E6S15_0474.rest = RH1E6S15_0474.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0474.s0 :: RH1E6S15_0474.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0474.s0.t = ((57800266243 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0474.s0]
  have e1 : RH1E6S15_0474.sL.t = ((57804669902 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0474.sL]
  rw [e0, e1] at h
  exact h

theorem band_0475 : RS5.BandZeros ((57804669902 : ℝ) / 65536) ((57809095034 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0475.s0 RH1E6S15_0475.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0475.s0 RH1E6S15_0475.rest = RH1E6S15_0475.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0475.s0 :: RH1E6S15_0475.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0475.s0.t = ((57804669902 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0475.s0]
  have e1 : RH1E6S15_0475.sL.t = ((57809095034 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0475.sL]
  rw [e0, e1] at h
  exact h

theorem part_059_1 : RS5.BandZeros ((57800266243 : ℝ) / 65536) ((57809095034 : ℝ) / 65536) 254 := by
  have g0 := band_0474
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0475
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((57800266243 : ℝ) / 65536) ((57809095034 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_059_1 <;> assumption
