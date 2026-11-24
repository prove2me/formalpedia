-- Prove2me | solution 1 for RH1E6S17.part_093_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T00:44:00.919139+00:00
-- url     : https://prove2.me/submissions/eeeee873-d195-47aa-bb5f-7d019585fe35

import Definitions.Def_RH1E6S17_D093_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0746 : RS5.BandZeros ((65523262311 : ℝ) / 65536) ((65527637053 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0746.s0 RH1E6S17_0746.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0746.s0 RH1E6S17_0746.rest = RH1E6S17_0746.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0746.s0 :: RH1E6S17_0746.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0746.s0.t = ((65523262311 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0746.s0]
  have e1 : RH1E6S17_0746.sL.t = ((65527637053 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0746.sL]
  rw [e0, e1] at h
  exact h

theorem band_0747 : RS5.BandZeros ((65527637053 : ℝ) / 65536) ((65532003175 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0747.s0 RH1E6S17_0747.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0747.s0 RH1E6S17_0747.rest = RH1E6S17_0747.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0747.s0 :: RH1E6S17_0747.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0747.s0.t = ((65527637053 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0747.s0]
  have e1 : RH1E6S17_0747.sL.t = ((65532003175 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0747.sL]
  rw [e0, e1] at h
  exact h

theorem part_093_1 : RS5.BandZeros ((65523262311 : ℝ) / 65536) ((65532003175 : ℝ) / 65536) 254 := by
  have g0 := band_0746
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0747
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((65523262311 : ℝ) / 65536) ((65532003175 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_093_1 <;> assumption
