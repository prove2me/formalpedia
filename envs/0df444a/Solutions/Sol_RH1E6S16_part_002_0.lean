-- Prove2me | solution 1 for RH1E6S16.part_002_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T13:59:40.690795+00:00
-- url     : https://prove2.me/submissions/ad84d20d-9a5e-4d68-95a9-e1c853d2a1d5

import Definitions.Def_RH1E6S16_D002_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0016 : RS5.BandZeros ((59052856022 : ℝ) / 65536) ((59057277740 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0016.s0 RH1E6S16_0016.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0016.s0 RH1E6S16_0016.rest = RH1E6S16_0016.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0016.s0 :: RH1E6S16_0016.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0016.s0.t = ((59052856022 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0016.s0]
  have e1 : RH1E6S16_0016.sL.t = ((59057277740 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0016.sL]
  rw [e0, e1] at h
  exact h

theorem band_0017 : RS5.BandZeros ((59057277740 : ℝ) / 65536) ((59061669365 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0017.s0 RH1E6S16_0017.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0017.s0 RH1E6S16_0017.rest = RH1E6S16_0017.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0017.s0 :: RH1E6S16_0017.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0017.s0.t = ((59057277740 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0017.s0]
  have e1 : RH1E6S16_0017.sL.t = ((59061669365 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0017.sL]
  rw [e0, e1] at h
  exact h

theorem part_002_0 : RS5.BandZeros ((59052856022 : ℝ) / 65536) ((59061669365 : ℝ) / 65536) 254 := by
  have g0 := band_0016
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0017
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((59052856022 : ℝ) / 65536) ((59061669365 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_002_0 <;> assumption
