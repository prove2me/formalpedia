-- Prove2me | solution 1 for RH1E6S13.part_049_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T23:35:18.183354+00:00
-- url     : https://prove2.me/submissions/adb6596e-0737-41be-8d40-f0793faabba6

import Definitions.Def_RH1E6S13_D049_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0392 : RS5.BandZeros ((50902994651 : ℝ) / 65536) ((50907454814 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0392.s0 RH1E6S13_0392.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0392.s0 RH1E6S13_0392.rest = RH1E6S13_0392.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0392.s0 :: RH1E6S13_0392.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0392.s0.t = ((50902994651 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0392.s0]
  have e1 : RH1E6S13_0392.sL.t = ((50907454814 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0392.sL]
  rw [e0, e1] at h
  exact h

theorem band_0393 : RS5.BandZeros ((50907454814 : ℝ) / 65536) ((50911906163 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0393.s0 RH1E6S13_0393.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0393.s0 RH1E6S13_0393.rest = RH1E6S13_0393.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0393.s0 :: RH1E6S13_0393.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0393.s0.t = ((50907454814 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0393.s0]
  have e1 : RH1E6S13_0393.sL.t = ((50911906163 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0393.sL]
  rw [e0, e1] at h
  exact h

theorem part_049_0 : RS5.BandZeros ((50902994651 : ℝ) / 65536) ((50911906163 : ℝ) / 65536) 254 := by
  have g0 := band_0392
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0393
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((50902994651 : ℝ) / 65536) ((50911906163 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_049_0 <;> assumption
