-- Prove2me | solution 1 for RH1E6S04.part_079_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T11:53:03.969552+00:00
-- url     : https://prove2.me/submissions/ac38577b-f14a-4749-842e-74b0a4281151

import Definitions.Def_RH1E6S04_D079_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0634 : RS5.BandZeros ((22717266071 : ℝ) / 65536) ((22722046360 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0634.s0 RH1E6S04_0634.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0634.s0 RH1E6S04_0634.rest = RH1E6S04_0634.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0634.s0 :: RH1E6S04_0634.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0634.s0.t = ((22717266071 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0634.s0]
  have e1 : RH1E6S04_0634.sL.t = ((22722046360 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0634.sL]
  rw [e0, e1] at h
  exact h

theorem band_0635 : RS5.BandZeros ((22722046360 : ℝ) / 65536) ((22726835986 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0635.s0 RH1E6S04_0635.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0635.s0 RH1E6S04_0635.rest = RH1E6S04_0635.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0635.s0 :: RH1E6S04_0635.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0635.s0.t = ((22722046360 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0635.s0]
  have e1 : RH1E6S04_0635.sL.t = ((22726835986 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0635.sL]
  rw [e0, e1] at h
  exact h

theorem part_079_1 : RS5.BandZeros ((22717266071 : ℝ) / 65536) ((22726835986 : ℝ) / 65536) 254 := by
  have g0 := band_0634
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0635
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((22717266071 : ℝ) / 65536) ((22726835986 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_079_1 <;> assumption
