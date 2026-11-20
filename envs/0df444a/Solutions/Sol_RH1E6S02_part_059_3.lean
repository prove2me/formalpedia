-- Prove2me | solution 1 for RH1E6S02.part_059_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T04:15:51.833083+00:00
-- url     : https://prove2.me/submissions/bd2c7aa5-7599-4437-94b4-16a7b3aff1bb

import Definitions.Def_RH1E6S02_D059_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0478 : RS5.BandZeros ((15498294361 : ℝ) / 65536) ((15503254326 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0478.s0 RH1E6S02_0478.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0478.s0 RH1E6S02_0478.rest = RH1E6S02_0478.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0478.s0 :: RH1E6S02_0478.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0478.s0.t = ((15498294361 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0478.s0]
  have e1 : RH1E6S02_0478.sL.t = ((15503254326 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0478.sL]
  rw [e0, e1] at h
  exact h

theorem band_0479 : RS5.BandZeros ((15503254326 : ℝ) / 65536) ((15508223404 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0479.s0 RH1E6S02_0479.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0479.s0 RH1E6S02_0479.rest = RH1E6S02_0479.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0479.s0 :: RH1E6S02_0479.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0479.s0.t = ((15503254326 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0479.s0]
  have e1 : RH1E6S02_0479.sL.t = ((15508223404 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0479.sL]
  rw [e0, e1] at h
  exact h

theorem part_059_3 : RS5.BandZeros ((15498294361 : ℝ) / 65536) ((15508223404 : ℝ) / 65536) 254 := by
  have g0 := band_0478
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0479
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((15498294361 : ℝ) / 65536) ((15508223404 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_059_3 <;> assumption
