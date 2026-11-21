-- Prove2me | solution 1 for RH1E6S05.part_075_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T16:18:03.198076+00:00
-- url     : https://prove2.me/submissions/9197e962-bccc-4a63-84f1-5ac0fcedb40e

import Definitions.Def_RH1E6S05_D075_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0606 : RS5.BandZeros ((25821706162 : ℝ) / 65536) ((25826431026 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0606.s0 RH1E6S05_0606.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0606.s0 RH1E6S05_0606.rest = RH1E6S05_0606.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0606.s0 :: RH1E6S05_0606.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0606.s0.t = ((25821706162 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0606.s0]
  have e1 : RH1E6S05_0606.sL.t = ((25826431026 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0606.sL]
  rw [e0, e1] at h
  exact h

theorem band_0607 : RS5.BandZeros ((25826431026 : ℝ) / 65536) ((25831174450 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0607.s0 RH1E6S05_0607.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0607.s0 RH1E6S05_0607.rest = RH1E6S05_0607.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0607.s0 :: RH1E6S05_0607.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0607.s0.t = ((25826431026 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0607.s0]
  have e1 : RH1E6S05_0607.sL.t = ((25831174450 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0607.sL]
  rw [e0, e1] at h
  exact h

theorem part_075_3 : RS5.BandZeros ((25821706162 : ℝ) / 65536) ((25831174450 : ℝ) / 65536) 254 := by
  have g0 := band_0606
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0607
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((25821706162 : ℝ) / 65536) ((25831174450 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_075_3 <;> assumption
