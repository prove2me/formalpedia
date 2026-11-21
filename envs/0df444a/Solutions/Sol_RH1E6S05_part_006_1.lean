-- Prove2me | solution 1 for RH1E6S05.part_006_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T12:20:51.868157+00:00
-- url     : https://prove2.me/submissions/2ca4ab7f-de0d-4bfe-bae0-94e04dcacc8f

import Definitions.Def_RH1E6S05_D006_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0050 : RS5.BandZeros ((23176764325 : ℝ) / 65536) ((23181545275 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0050.s0 RH1E6S05_0050.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0050.s0 RH1E6S05_0050.rest = RH1E6S05_0050.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0050.s0 :: RH1E6S05_0050.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0050.s0.t = ((23176764325 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0050.s0]
  have e1 : RH1E6S05_0050.sL.t = ((23181545275 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0050.sL]
  rw [e0, e1] at h
  exact h

theorem band_0051 : RS5.BandZeros ((23181545275 : ℝ) / 65536) ((23186316724 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0051.s0 RH1E6S05_0051.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0051.s0 RH1E6S05_0051.rest = RH1E6S05_0051.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0051.s0 :: RH1E6S05_0051.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0051.s0.t = ((23181545275 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0051.s0]
  have e1 : RH1E6S05_0051.sL.t = ((23186316724 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0051.sL]
  rw [e0, e1] at h
  exact h

theorem part_006_1 : RS5.BandZeros ((23176764325 : ℝ) / 65536) ((23186316724 : ℝ) / 65536) 254 := by
  have g0 := band_0050
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0051
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((23176764325 : ℝ) / 65536) ((23186316724 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_006_1 <;> assumption
