-- Prove2me | solution 1 for RH1E6S09.part_061_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T13:24:37.452119+00:00
-- url     : https://prove2.me/submissions/79ccada3-f45c-4501-b0f7-fe36bd7a8264

import Definitions.Def_RH1E6S09_D061_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0492 : RS5.BandZeros ((38299671229 : ℝ) / 65536) ((38304248187 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0492.s0 RH1E6S09_0492.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0492.s0 RH1E6S09_0492.rest = RH1E6S09_0492.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0492.s0 :: RH1E6S09_0492.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0492.s0.t = ((38299671229 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0492.s0]
  have e1 : RH1E6S09_0492.sL.t = ((38304248187 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0492.sL]
  rw [e0, e1] at h
  exact h

theorem band_0493 : RS5.BandZeros ((38304248187 : ℝ) / 65536) ((38308804309 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0493.s0 RH1E6S09_0493.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0493.s0 RH1E6S09_0493.rest = RH1E6S09_0493.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0493.s0 :: RH1E6S09_0493.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0493.s0.t = ((38304248187 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0493.s0]
  have e1 : RH1E6S09_0493.sL.t = ((38308804309 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0493.sL]
  rw [e0, e1] at h
  exact h

theorem part_061_2 : RS5.BandZeros ((38299671229 : ℝ) / 65536) ((38308804309 : ℝ) / 65536) 254 := by
  have g0 := band_0492
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0493
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((38299671229 : ℝ) / 65536) ((38308804309 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_061_2 <;> assumption
