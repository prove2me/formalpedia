-- Prove2me | solution 1 for RH1E6S16.part_061_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T17:50:19.839595+00:00
-- url     : https://prove2.me/submissions/05dc2862-28b6-43df-bff6-a652317400f2

import Definitions.Def_RH1E6S16_D061_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0488 : RS5.BandZeros ((61128683026 : ℝ) / 65536) ((61133091916 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0488.s0 RH1E6S16_0488.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0488.s0 RH1E6S16_0488.rest = RH1E6S16_0488.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0488.s0 :: RH1E6S16_0488.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0488.s0.t = ((61128683026 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0488.s0]
  have e1 : RH1E6S16_0488.sL.t = ((61133091916 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0488.sL]
  rw [e0, e1] at h
  exact h

theorem band_0489 : RS5.BandZeros ((61133091916 : ℝ) / 65536) ((61137484228 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0489.s0 RH1E6S16_0489.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0489.s0 RH1E6S16_0489.rest = RH1E6S16_0489.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0489.s0 :: RH1E6S16_0489.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0489.s0.t = ((61133091916 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0489.s0]
  have e1 : RH1E6S16_0489.sL.t = ((61137484228 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0489.sL]
  rw [e0, e1] at h
  exact h

theorem part_061_0 : RS5.BandZeros ((61128683026 : ℝ) / 65536) ((61137484228 : ℝ) / 65536) 254 := by
  have g0 := band_0488
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0489
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((61128683026 : ℝ) / 65536) ((61137484228 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_061_0 <;> assumption
