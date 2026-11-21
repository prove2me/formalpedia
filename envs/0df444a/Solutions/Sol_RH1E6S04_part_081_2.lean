-- Prove2me | solution 1 for RH1E6S04.part_081_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T11:55:48.72564+00:00
-- url     : https://prove2.me/submissions/400cae5a-42e3-45ab-8e34-eeba566664a6

import Definitions.Def_RH1E6S04_D081_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0652 : RS5.BandZeros ((22803457435 : ℝ) / 65536) ((22808245492 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0652.s0 RH1E6S04_0652.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0652.s0 RH1E6S04_0652.rest = RH1E6S04_0652.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0652.s0 :: RH1E6S04_0652.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0652.s0.t = ((22803457435 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0652.s0]
  have e1 : RH1E6S04_0652.sL.t = ((22808245492 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0652.sL]
  rw [e0, e1] at h
  exact h

theorem band_0653 : RS5.BandZeros ((22808245492 : ℝ) / 65536) ((22813024032 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0653.s0 RH1E6S04_0653.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0653.s0 RH1E6S04_0653.rest = RH1E6S04_0653.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0653.s0 :: RH1E6S04_0653.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0653.s0.t = ((22808245492 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0653.s0]
  have e1 : RH1E6S04_0653.sL.t = ((22813024032 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0653.sL]
  rw [e0, e1] at h
  exact h

theorem part_081_2 : RS5.BandZeros ((22803457435 : ℝ) / 65536) ((22813024032 : ℝ) / 65536) 254 := by
  have g0 := band_0652
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0653
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((22803457435 : ℝ) / 65536) ((22813024032 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_081_2 <;> assumption
