-- Prove2me | solution 1 for RH1E6S04.part_027_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T09:25:26.671181+00:00
-- url     : https://prove2.me/submissions/32fc09c0-bd5e-4b5a-b0b3-335cca525fd0

import Definitions.Def_RH1E6S04_D027_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0218 : RS5.BandZeros ((20716405905 : ℝ) / 65536) ((20721236408 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0218.s0 RH1E6S04_0218.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0218.s0 RH1E6S04_0218.rest = RH1E6S04_0218.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0218.s0 :: RH1E6S04_0218.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0218.s0.t = ((20716405905 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0218.s0]
  have e1 : RH1E6S04_0218.sL.t = ((20721236408 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0218.sL]
  rw [e0, e1] at h
  exact h

theorem band_0219 : RS5.BandZeros ((20721236408 : ℝ) / 65536) ((20726057300 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0219.s0 RH1E6S04_0219.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0219.s0 RH1E6S04_0219.rest = RH1E6S04_0219.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0219.s0 :: RH1E6S04_0219.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0219.s0.t = ((20721236408 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0219.s0]
  have e1 : RH1E6S04_0219.sL.t = ((20726057300 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0219.sL]
  rw [e0, e1] at h
  exact h

theorem part_027_1 : RS5.BandZeros ((20716405905 : ℝ) / 65536) ((20726057300 : ℝ) / 65536) 254 := by
  have g0 := band_0218
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0219
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((20716405905 : ℝ) / 65536) ((20726057300 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_027_1 <;> assumption
