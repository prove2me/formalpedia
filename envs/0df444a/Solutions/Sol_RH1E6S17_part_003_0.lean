-- Prove2me | solution 1 for RH1E6S17.part_003_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T19:43:45.708801+00:00
-- url     : https://prove2.me/submissions/a9e95caf-8990-4bf0-a251-20241fa88e97

import Definitions.Def_RH1E6S17_D003_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0024 : RS5.BandZeros ((62364425028 : ℝ) / 65536) ((62368817891 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0024.s0 RH1E6S17_0024.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0024.s0 RH1E6S17_0024.rest = RH1E6S17_0024.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0024.s0 :: RH1E6S17_0024.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0024.s0.t = ((62364425028 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0024.s0]
  have e1 : RH1E6S17_0024.sL.t = ((62368817891 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0024.sL]
  rw [e0, e1] at h
  exact h

theorem band_0025 : RS5.BandZeros ((62368817891 : ℝ) / 65536) ((62373202097 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0025.s0 RH1E6S17_0025.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0025.s0 RH1E6S17_0025.rest = RH1E6S17_0025.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0025.s0 :: RH1E6S17_0025.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0025.s0.t = ((62368817891 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0025.s0]
  have e1 : RH1E6S17_0025.sL.t = ((62373202097 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0025.sL]
  rw [e0, e1] at h
  exact h

theorem part_003_0 : RS5.BandZeros ((62364425028 : ℝ) / 65536) ((62373202097 : ℝ) / 65536) 254 := by
  have g0 := band_0024
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0025
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((62364425028 : ℝ) / 65536) ((62373202097 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_003_0 <;> assumption
