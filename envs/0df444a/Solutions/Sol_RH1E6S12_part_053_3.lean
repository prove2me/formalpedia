-- Prove2me | solution 1 for RH1E6S12.part_053_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T10:02:35.690811+00:00
-- url     : https://prove2.me/submissions/5839e84b-2e57-4438-baab-85398fb484a7

import Definitions.Def_RH1E6S12_D053_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0430 : RS5.BandZeros ((47806806466 : ℝ) / 65536) ((47811299368 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0430.s0 RH1E6S12_0430.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0430.s0 RH1E6S12_0430.rest = RH1E6S12_0430.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0430.s0 :: RH1E6S12_0430.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0430.s0.t = ((47806806466 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0430.s0]
  have e1 : RH1E6S12_0430.sL.t = ((47811299368 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0430.sL]
  rw [e0, e1] at h
  exact h

theorem band_0431 : RS5.BandZeros ((47811299368 : ℝ) / 65536) ((47815787414 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0431.s0 RH1E6S12_0431.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0431.s0 RH1E6S12_0431.rest = RH1E6S12_0431.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0431.s0 :: RH1E6S12_0431.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0431.s0.t = ((47811299368 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0431.s0]
  have e1 : RH1E6S12_0431.sL.t = ((47815787414 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0431.sL]
  rw [e0, e1] at h
  exact h

theorem part_053_3 : RS5.BandZeros ((47806806466 : ℝ) / 65536) ((47815787414 : ℝ) / 65536) 254 := by
  have g0 := band_0430
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0431
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((47806806466 : ℝ) / 65536) ((47815787414 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_053_3 <;> assumption
