-- Prove2me | solution 1 for RH1E6S00.part_061_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T22:50:10.717669+00:00
-- url     : https://prove2.me/submissions/ed615f92-eac6-4d49-b96b-35185bd0690d

import Definitions.Def_RH1E6S00_D061_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0492 : RS5.BandZeros ((9165155801 : ℝ) / 65536) ((9170390020 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0492.s0 RH1E6S00_0492.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0492.s0 RH1E6S00_0492.rest = RH1E6S00_0492.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0492.s0 :: RH1E6S00_0492.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0492.s0.t = ((9165155801 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0492.s0]
  have e1 : RH1E6S00_0492.sL.t = ((9170390020 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0492.sL]
  rw [e0, e1] at h
  exact h

theorem band_0493 : RS5.BandZeros ((9170390020 : ℝ) / 65536) ((9175623941 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0493.s0 RH1E6S00_0493.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0493.s0 RH1E6S00_0493.rest = RH1E6S00_0493.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0493.s0 :: RH1E6S00_0493.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0493.s0.t = ((9170390020 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0493.s0]
  have e1 : RH1E6S00_0493.sL.t = ((9175623941 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0493.sL]
  rw [e0, e1] at h
  exact h

theorem part_061_2 : RS5.BandZeros ((9165155801 : ℝ) / 65536) ((9175623941 : ℝ) / 65536) 254 := by
  have g0 := band_0492
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0493
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((9165155801 : ℝ) / 65536) ((9175623941 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_061_2 <;> assumption
