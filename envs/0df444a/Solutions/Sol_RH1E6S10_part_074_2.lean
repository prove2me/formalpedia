-- Prove2me | solution 1 for RH1E6S10.part_074_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T02:18:42.662826+00:00
-- url     : https://prove2.me/submissions/fd210f75-a87b-4a8c-9a23-f16450579d69

import Definitions.Def_RH1E6S10_D074_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0596 : RS5.BandZeros ((42031768819 : ℝ) / 65536) ((42036303032 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0596.s0 RH1E6S10_0596.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0596.s0 RH1E6S10_0596.rest = RH1E6S10_0596.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0596.s0 :: RH1E6S10_0596.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0596.s0.t = ((42031768819 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0596.s0]
  have e1 : RH1E6S10_0596.sL.t = ((42036303032 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0596.sL]
  rw [e0, e1] at h
  exact h

theorem band_0597 : RS5.BandZeros ((42036303032 : ℝ) / 65536) ((42040837202 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0597.s0 RH1E6S10_0597.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0597.s0 RH1E6S10_0597.rest = RH1E6S10_0597.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0597.s0 :: RH1E6S10_0597.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0597.s0.t = ((42036303032 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0597.s0]
  have e1 : RH1E6S10_0597.sL.t = ((42040837202 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0597.sL]
  rw [e0, e1] at h
  exact h

theorem part_074_2 : RS5.BandZeros ((42031768819 : ℝ) / 65536) ((42040837202 : ℝ) / 65536) 254 := by
  have g0 := band_0596
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0597
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((42031768819 : ℝ) / 65536) ((42040837202 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_074_2 <;> assumption
