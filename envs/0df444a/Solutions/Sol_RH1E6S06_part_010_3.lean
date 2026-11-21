-- Prove2me | solution 1 for RH1E6S06.part_010_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T17:40:46.954309+00:00
-- url     : https://prove2.me/submissions/b8d67ab8-0824-4250-9440-4bf527379856

import Definitions.Def_RH1E6S06_D010_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0086 : RS5.BandZeros ((26620707655 : ℝ) / 65536) ((26625431176 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0086.s0 RH1E6S06_0086.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0086.s0 RH1E6S06_0086.rest = RH1E6S06_0086.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0086.s0 :: RH1E6S06_0086.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0086.s0.t = ((26620707655 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0086.s0]
  have e1 : RH1E6S06_0086.sL.t = ((26625431176 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0086.sL]
  rw [e0, e1] at h
  exact h

theorem band_0087 : RS5.BandZeros ((26625431176 : ℝ) / 65536) ((26630149793 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0087.s0 RH1E6S06_0087.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0087.s0 RH1E6S06_0087.rest = RH1E6S06_0087.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0087.s0 :: RH1E6S06_0087.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0087.s0.t = ((26625431176 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0087.s0]
  have e1 : RH1E6S06_0087.sL.t = ((26630149793 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0087.sL]
  rw [e0, e1] at h
  exact h

theorem part_010_3 : RS5.BandZeros ((26620707655 : ℝ) / 65536) ((26630149793 : ℝ) / 65536) 254 := by
  have g0 := band_0086
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0087
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((26620707655 : ℝ) / 65536) ((26630149793 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_010_3 <;> assumption
