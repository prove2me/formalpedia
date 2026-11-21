-- Prove2me | solution 1 for RH1E6S04.part_078_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T11:49:47.791613+00:00
-- url     : https://prove2.me/submissions/058447ac-f1da-4409-b0f3-55c64748ef9a

import Definitions.Def_RH1E6S04_D078_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0624 : RS5.BandZeros ((22669344943 : ℝ) / 65536) ((22674135587 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0624.s0 RH1E6S04_0624.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0624.s0 RH1E6S04_0624.rest = RH1E6S04_0624.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0624.s0 :: RH1E6S04_0624.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0624.s0.t = ((22669344943 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0624.s0]
  have e1 : RH1E6S04_0624.sL.t = ((22674135587 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0624.sL]
  rw [e0, e1] at h
  exact h

theorem band_0625 : RS5.BandZeros ((22674135587 : ℝ) / 65536) ((22678935569 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0625.s0 RH1E6S04_0625.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0625.s0 RH1E6S04_0625.rest = RH1E6S04_0625.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0625.s0 :: RH1E6S04_0625.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0625.s0.t = ((22674135587 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0625.s0]
  have e1 : RH1E6S04_0625.sL.t = ((22678935569 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0625.sL]
  rw [e0, e1] at h
  exact h

theorem part_078_0 : RS5.BandZeros ((22669344943 : ℝ) / 65536) ((22678935569 : ℝ) / 65536) 254 := by
  have g0 := band_0624
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0625
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((22669344943 : ℝ) / 65536) ((22678935569 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_078_0 <;> assumption
