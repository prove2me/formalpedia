-- Prove2me | solution 1 for RH1E6S14.part_004_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T02:42:45.004955+00:00
-- url     : https://prove2.me/submissions/440afd37-3dff-4bd4-8fc8-ba605a255f77

import Definitions.Def_RH1E6S14_D004_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0036 : RS5.BandZeros ((52588915063 : ℝ) / 65536) ((52593387840 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0036.s0 RH1E6S14_0036.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0036.s0 RH1E6S14_0036.rest = RH1E6S14_0036.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0036.s0 :: RH1E6S14_0036.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0036.s0.t = ((52588915063 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0036.s0]
  have e1 : RH1E6S14_0036.sL.t = ((52593387840 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0036.sL]
  rw [e0, e1] at h
  exact h

theorem band_0037 : RS5.BandZeros ((52593387840 : ℝ) / 65536) ((52597819810 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0037.s0 RH1E6S14_0037.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0037.s0 RH1E6S14_0037.rest = RH1E6S14_0037.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0037.s0 :: RH1E6S14_0037.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0037.s0.t = ((52593387840 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0037.s0]
  have e1 : RH1E6S14_0037.sL.t = ((52597819810 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0037.sL]
  rw [e0, e1] at h
  exact h

theorem part_004_2 : RS5.BandZeros ((52588915063 : ℝ) / 65536) ((52597819810 : ℝ) / 65536) 254 := by
  have g0 := band_0036
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0037
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((52588915063 : ℝ) / 65536) ((52597819810 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_004_2 <;> assumption
