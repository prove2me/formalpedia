-- Prove2me | solution 1 for RH1E6S17.part_004_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T19:47:00.752884+00:00
-- url     : https://prove2.me/submissions/cd0bc746-8a71-4bc6-89c4-c7ae150b3a76

import Definitions.Def_RH1E6S17_D004_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0036 : RS5.BandZeros ((62417051371 : ℝ) / 65536) ((62421418033 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0036.s0 RH1E6S17_0036.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0036.s0 RH1E6S17_0036.rest = RH1E6S17_0036.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0036.s0 :: RH1E6S17_0036.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0036.s0.t = ((62417051371 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0036.s0]
  have e1 : RH1E6S17_0036.sL.t = ((62421418033 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0036.sL]
  rw [e0, e1] at h
  exact h

theorem band_0037 : RS5.BandZeros ((62421418033 : ℝ) / 65536) ((62425810560 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0037.s0 RH1E6S17_0037.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0037.s0 RH1E6S17_0037.rest = RH1E6S17_0037.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0037.s0 :: RH1E6S17_0037.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0037.s0.t = ((62421418033 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0037.s0]
  have e1 : RH1E6S17_0037.sL.t = ((62425810560 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0037.sL]
  rw [e0, e1] at h
  exact h

theorem part_004_2 : RS5.BandZeros ((62417051371 : ℝ) / 65536) ((62425810560 : ℝ) / 65536) 254 := by
  have g0 := band_0036
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0037
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((62417051371 : ℝ) / 65536) ((62425810560 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_004_2 <;> assumption
