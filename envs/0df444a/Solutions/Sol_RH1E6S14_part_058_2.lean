-- Prove2me | solution 1 for RH1E6S14.part_058_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T05:50:05.112029+00:00
-- url     : https://prove2.me/submissions/916039b5-3b27-42cb-bc54-8d0ca16008ac

import Definitions.Def_RH1E6S14_D058_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0468 : RS5.BandZeros ((54507459126 : ℝ) / 65536) ((54511882384 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0468.s0 RH1E6S14_0468.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0468.s0 RH1E6S14_0468.rest = RH1E6S14_0468.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0468.s0 :: RH1E6S14_0468.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0468.s0.t = ((54507459126 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0468.s0]
  have e1 : RH1E6S14_0468.sL.t = ((54511882384 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0468.sL]
  rw [e0, e1] at h
  exact h

theorem band_0469 : RS5.BandZeros ((54511882384 : ℝ) / 65536) ((54516341912 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0469.s0 RH1E6S14_0469.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0469.s0 RH1E6S14_0469.rest = RH1E6S14_0469.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0469.s0 :: RH1E6S14_0469.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0469.s0.t = ((54511882384 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0469.s0]
  have e1 : RH1E6S14_0469.sL.t = ((54516341912 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0469.sL]
  rw [e0, e1] at h
  exact h

theorem part_058_2 : RS5.BandZeros ((54507459126 : ℝ) / 65536) ((54516341912 : ℝ) / 65536) 254 := by
  have g0 := band_0468
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0469
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((54507459126 : ℝ) / 65536) ((54516341912 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_058_2 <;> assumption
