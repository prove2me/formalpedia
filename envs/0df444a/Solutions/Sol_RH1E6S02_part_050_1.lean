-- Prove2me | solution 1 for RH1E6S02.part_050_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T03:54:05.668445+00:00
-- url     : https://prove2.me/submissions/ebc3f58d-8b7a-4f84-9e22-0fa5d829cdd0

import Definitions.Def_RH1E6S02_D050_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0402 : RS5.BandZeros ((15120614725 : ℝ) / 65536) ((15125606882 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0402.s0 RH1E6S02_0402.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0402.s0 RH1E6S02_0402.rest = RH1E6S02_0402.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0402.s0 :: RH1E6S02_0402.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0402.s0.t = ((15120614725 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0402.s0]
  have e1 : RH1E6S02_0402.sL.t = ((15125606882 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0402.sL]
  rw [e0, e1] at h
  exact h

theorem band_0403 : RS5.BandZeros ((15125606882 : ℝ) / 65536) ((15130579363 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0403.s0 RH1E6S02_0403.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0403.s0 RH1E6S02_0403.rest = RH1E6S02_0403.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0403.s0 :: RH1E6S02_0403.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0403.s0.t = ((15125606882 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0403.s0]
  have e1 : RH1E6S02_0403.sL.t = ((15130579363 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0403.sL]
  rw [e0, e1] at h
  exact h

theorem part_050_1 : RS5.BandZeros ((15120614725 : ℝ) / 65536) ((15130579363 : ℝ) / 65536) 254 := by
  have g0 := band_0402
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0403
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((15120614725 : ℝ) / 65536) ((15130579363 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_050_1 <;> assumption
