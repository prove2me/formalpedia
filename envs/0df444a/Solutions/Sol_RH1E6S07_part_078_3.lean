-- Prove2me | solution 1 for RH1E6S07.part_078_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T02:38:46.941572+00:00
-- url     : https://prove2.me/submissions/200f32b7-160d-42d2-9fdc-c33fb78ac968

import Definitions.Def_RH1E6S07_D078_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0630 : RS5.BandZeros ((32425651202 : ℝ) / 65536) ((32430296711 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0630.s0 RH1E6S07_0630.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0630.s0 RH1E6S07_0630.rest = RH1E6S07_0630.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0630.s0 :: RH1E6S07_0630.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0630.s0.t = ((32425651202 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0630.s0]
  have e1 : RH1E6S07_0630.sL.t = ((32430296711 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0630.sL]
  rw [e0, e1] at h
  exact h

theorem band_0631 : RS5.BandZeros ((32430296711 : ℝ) / 65536) ((32434948972 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0631.s0 RH1E6S07_0631.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0631.s0 RH1E6S07_0631.rest = RH1E6S07_0631.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0631.s0 :: RH1E6S07_0631.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0631.s0.t = ((32430296711 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0631.s0]
  have e1 : RH1E6S07_0631.sL.t = ((32434948972 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0631.sL]
  rw [e0, e1] at h
  exact h

theorem part_078_3 : RS5.BandZeros ((32425651202 : ℝ) / 65536) ((32434948972 : ℝ) / 65536) 254 := by
  have g0 := band_0630
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0631
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((32425651202 : ℝ) / 65536) ((32434948972 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_078_3 <;> assumption
