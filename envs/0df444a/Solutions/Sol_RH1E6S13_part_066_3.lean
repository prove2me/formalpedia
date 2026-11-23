-- Prove2me | solution 1 for RH1E6S13.part_066_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T01:02:04.871802+00:00
-- url     : https://prove2.me/submissions/415a0594-4475-4926-9325-49babfbcd205

import Definitions.Def_RH1E6S13_D066_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0534 : RS5.BandZeros ((51536005796 : ℝ) / 65536) ((51540452492 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0534.s0 RH1E6S13_0534.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0534.s0 RH1E6S13_0534.rest = RH1E6S13_0534.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0534.s0 :: RH1E6S13_0534.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0534.s0.t = ((51536005796 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0534.s0]
  have e1 : RH1E6S13_0534.sL.t = ((51540452492 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0534.sL]
  rw [e0, e1] at h
  exact h

theorem band_0535 : RS5.BandZeros ((51540452492 : ℝ) / 65536) ((51544925467 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0535.s0 RH1E6S13_0535.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0535.s0 RH1E6S13_0535.rest = RH1E6S13_0535.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0535.s0 :: RH1E6S13_0535.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0535.s0.t = ((51540452492 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0535.s0]
  have e1 : RH1E6S13_0535.sL.t = ((51544925467 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0535.sL]
  rw [e0, e1] at h
  exact h

theorem part_066_3 : RS5.BandZeros ((51536005796 : ℝ) / 65536) ((51544925467 : ℝ) / 65536) 254 := by
  have g0 := band_0534
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0535
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((51536005796 : ℝ) / 65536) ((51544925467 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_066_3 <;> assumption
