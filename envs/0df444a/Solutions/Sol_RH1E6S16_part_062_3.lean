-- Prove2me | solution 1 for RH1E6S16.part_062_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T17:53:41.0596+00:00
-- url     : https://prove2.me/submissions/a7942ab1-913e-44e5-9acd-8c05aa52c34b

import Definitions.Def_RH1E6S16_D062_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0502 : RS5.BandZeros ((61190184061 : ℝ) / 65536) ((61194565409 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0502.s0 RH1E6S16_0502.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0502.s0 RH1E6S16_0502.rest = RH1E6S16_0502.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0502.s0 :: RH1E6S16_0502.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0502.s0.t = ((61190184061 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0502.s0]
  have e1 : RH1E6S16_0502.sL.t = ((61194565409 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0502.sL]
  rw [e0, e1] at h
  exact h

theorem band_0503 : RS5.BandZeros ((61194565409 : ℝ) / 65536) ((61198963286 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0503.s0 RH1E6S16_0503.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0503.s0 RH1E6S16_0503.rest = RH1E6S16_0503.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0503.s0 :: RH1E6S16_0503.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0503.s0.t = ((61194565409 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0503.s0]
  have e1 : RH1E6S16_0503.sL.t = ((61198963286 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0503.sL]
  rw [e0, e1] at h
  exact h

theorem part_062_3 : RS5.BandZeros ((61190184061 : ℝ) / 65536) ((61198963286 : ℝ) / 65536) 254 := by
  have g0 := band_0502
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0503
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((61190184061 : ℝ) / 65536) ((61198963286 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_062_3 <;> assumption
