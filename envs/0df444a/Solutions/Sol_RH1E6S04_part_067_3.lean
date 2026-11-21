-- Prove2me | solution 1 for RH1E6S04.part_067_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T10:57:59.244421+00:00
-- url     : https://prove2.me/submissions/1cfff871-4579-42e0-8d46-ef5ecca5df50

import Definitions.Def_RH1E6S04_D067_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0542 : RS5.BandZeros ((22276194201 : ℝ) / 65536) ((22281001979 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0542.s0 RH1E6S04_0542.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0542.s0 RH1E6S04_0542.rest = RH1E6S04_0542.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0542.s0 :: RH1E6S04_0542.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0542.s0.t = ((22276194201 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0542.s0]
  have e1 : RH1E6S04_0542.sL.t = ((22281001979 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0542.sL]
  rw [e0, e1] at h
  exact h

theorem band_0543 : RS5.BandZeros ((22281001979 : ℝ) / 65536) ((22285809663 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0543.s0 RH1E6S04_0543.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0543.s0 RH1E6S04_0543.rest = RH1E6S04_0543.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0543.s0 :: RH1E6S04_0543.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0543.s0.t = ((22281001979 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0543.s0]
  have e1 : RH1E6S04_0543.sL.t = ((22285809663 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0543.sL]
  rw [e0, e1] at h
  exact h

theorem part_067_3 : RS5.BandZeros ((22276194201 : ℝ) / 65536) ((22285809663 : ℝ) / 65536) 254 := by
  have g0 := band_0542
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0543
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((22276194201 : ℝ) / 65536) ((22285809663 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_067_3 <;> assumption
