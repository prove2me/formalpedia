-- Prove2me | solution 1 for RH1E6S15.part_080_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T12:57:23.231802+00:00
-- url     : https://prove2.me/submissions/2168cd50-258a-4bfc-9174-0e0021a43b5c

import Definitions.Def_RH1E6S15_D080_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0640 : RS5.BandZeros ((58532333701 : ℝ) / 65536) ((58536727379 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0640.s0 RH1E6S15_0640.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0640.s0 RH1E6S15_0640.rest = RH1E6S15_0640.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0640.s0 :: RH1E6S15_0640.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0640.s0.t = ((58532333701 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0640.s0]
  have e1 : RH1E6S15_0640.sL.t = ((58536727379 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0640.sL]
  rw [e0, e1] at h
  exact h

theorem band_0641 : RS5.BandZeros ((58536727379 : ℝ) / 65536) ((58541148858 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0641.s0 RH1E6S15_0641.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0641.s0 RH1E6S15_0641.rest = RH1E6S15_0641.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0641.s0 :: RH1E6S15_0641.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0641.s0.t = ((58536727379 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0641.s0]
  have e1 : RH1E6S15_0641.sL.t = ((58541148858 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0641.sL]
  rw [e0, e1] at h
  exact h

theorem part_080_0 : RS5.BandZeros ((58532333701 : ℝ) / 65536) ((58541148858 : ℝ) / 65536) 254 := by
  have g0 := band_0640
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0641
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((58532333701 : ℝ) / 65536) ((58541148858 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_080_0 <;> assumption
