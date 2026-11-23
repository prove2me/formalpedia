-- Prove2me | solution 1 for RH1E6S14.part_068_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T06:22:47.536594+00:00
-- url     : https://prove2.me/submissions/987d2df8-b2e7-436f-8d82-bb02e75d7e5d

import Definitions.Def_RH1E6S14_D068_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0550 : RS5.BandZeros ((54870979488 : ℝ) / 65536) ((54875399058 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0550.s0 RH1E6S14_0550.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0550.s0 RH1E6S14_0550.rest = RH1E6S14_0550.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0550.s0 :: RH1E6S14_0550.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0550.s0.t = ((54870979488 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0550.s0]
  have e1 : RH1E6S14_0550.sL.t = ((54875399058 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0550.sL]
  rw [e0, e1] at h
  exact h

theorem band_0551 : RS5.BandZeros ((54875399058 : ℝ) / 65536) ((54879834798 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0551.s0 RH1E6S14_0551.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0551.s0 RH1E6S14_0551.rest = RH1E6S14_0551.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0551.s0 :: RH1E6S14_0551.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0551.s0.t = ((54875399058 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0551.s0]
  have e1 : RH1E6S14_0551.sL.t = ((54879834798 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0551.sL]
  rw [e0, e1] at h
  exact h

theorem part_068_3 : RS5.BandZeros ((54870979488 : ℝ) / 65536) ((54879834798 : ℝ) / 65536) 254 := by
  have g0 := band_0550
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0551
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((54870979488 : ℝ) / 65536) ((54879834798 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_068_3 <;> assumption
