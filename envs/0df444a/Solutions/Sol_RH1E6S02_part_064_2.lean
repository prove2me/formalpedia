-- Prove2me | solution 1 for RH1E6S02.part_064_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T04:25:41.38783+00:00
-- url     : https://prove2.me/submissions/769079e0-a354-4a02-b5f7-f75c9a07dac5

import Definitions.Def_RH1E6S02_D064_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0516 : RS5.BandZeros ((15686805808 : ℝ) / 65536) ((15691772827 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0516.s0 RH1E6S02_0516.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0516.s0 RH1E6S02_0516.rest = RH1E6S02_0516.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0516.s0 :: RH1E6S02_0516.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0516.s0.t = ((15686805808 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0516.s0]
  have e1 : RH1E6S02_0516.sL.t = ((15691772827 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0516.sL]
  rw [e0, e1] at h
  exact h

theorem band_0517 : RS5.BandZeros ((15691772827 : ℝ) / 65536) ((15696720764 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0517.s0 RH1E6S02_0517.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0517.s0 RH1E6S02_0517.rest = RH1E6S02_0517.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0517.s0 :: RH1E6S02_0517.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0517.s0.t = ((15691772827 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0517.s0]
  have e1 : RH1E6S02_0517.sL.t = ((15696720764 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0517.sL]
  rw [e0, e1] at h
  exact h

theorem part_064_2 : RS5.BandZeros ((15686805808 : ℝ) / 65536) ((15696720764 : ℝ) / 65536) 254 := by
  have g0 := band_0516
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0517
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((15686805808 : ℝ) / 65536) ((15696720764 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_064_2 <;> assumption
