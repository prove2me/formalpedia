-- Prove2me | solution 1 for RH1E6S17.part_012_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T20:14:56.11112+00:00
-- url     : https://prove2.me/submissions/1a362720-3b1d-404a-be74-e97ef605f077

import Definitions.Def_RH1E6S17_D012_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0100 : RS5.BandZeros ((62697535954 : ℝ) / 65536) ((62701961361 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0100.s0 RH1E6S17_0100.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0100.s0 RH1E6S17_0100.rest = RH1E6S17_0100.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0100.s0 :: RH1E6S17_0100.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0100.s0.t = ((62697535954 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0100.s0]
  have e1 : RH1E6S17_0100.sL.t = ((62701961361 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0100.sL]
  rw [e0, e1] at h
  exact h

theorem band_0101 : RS5.BandZeros ((62701961361 : ℝ) / 65536) ((62706334984 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0101.s0 RH1E6S17_0101.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0101.s0 RH1E6S17_0101.rest = RH1E6S17_0101.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0101.s0 :: RH1E6S17_0101.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0101.s0.t = ((62701961361 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0101.s0]
  have e1 : RH1E6S17_0101.sL.t = ((62706334984 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0101.sL]
  rw [e0, e1] at h
  exact h

theorem part_012_2 : RS5.BandZeros ((62697535954 : ℝ) / 65536) ((62706334984 : ℝ) / 65536) 254 := by
  have g0 := band_0100
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0101
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((62697535954 : ℝ) / 65536) ((62706334984 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_012_2 <;> assumption
