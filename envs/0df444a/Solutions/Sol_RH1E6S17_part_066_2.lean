-- Prove2me | solution 1 for RH1E6S17.part_066_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T23:17:24.97679+00:00
-- url     : https://prove2.me/submissions/82bba0b2-3a10-4eb9-b247-cceee4e67547

import Definitions.Def_RH1E6S17_D066_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0532 : RS5.BandZeros ((64588353346 : ℝ) / 65536) ((64592698923 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0532.s0 RH1E6S17_0532.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0532.s0 RH1E6S17_0532.rest = RH1E6S17_0532.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0532.s0 :: RH1E6S17_0532.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0532.s0.t = ((64588353346 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0532.s0]
  have e1 : RH1E6S17_0532.sL.t = ((64592698923 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0532.sL]
  rw [e0, e1] at h
  exact h

theorem band_0533 : RS5.BandZeros ((64592698923 : ℝ) / 65536) ((64597096105 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0533.s0 RH1E6S17_0533.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0533.s0 RH1E6S17_0533.rest = RH1E6S17_0533.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0533.s0 :: RH1E6S17_0533.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0533.s0.t = ((64592698923 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0533.s0]
  have e1 : RH1E6S17_0533.sL.t = ((64597096105 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0533.sL]
  rw [e0, e1] at h
  exact h

theorem part_066_2 : RS5.BandZeros ((64588353346 : ℝ) / 65536) ((64597096105 : ℝ) / 65536) 254 := by
  have g0 := band_0532
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0533
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((64588353346 : ℝ) / 65536) ((64597096105 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_066_2 <;> assumption
