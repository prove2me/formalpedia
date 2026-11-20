-- Prove2me | solution 1 for RH1E6S02.part_080_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T04:59:45.197313+00:00
-- url     : https://prove2.me/submissions/c103cb59-c860-4dbb-96e2-b554fdc88def

import Definitions.Def_RH1E6S02_D080_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0640 : RS5.BandZeros ((16300456843 : ℝ) / 65536) ((16305403216 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0640.s0 RH1E6S02_0640.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0640.s0 RH1E6S02_0640.rest = RH1E6S02_0640.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0640.s0 :: RH1E6S02_0640.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0640.s0.t = ((16300456843 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0640.s0]
  have e1 : RH1E6S02_0640.sL.t = ((16305403216 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0640.sL]
  rw [e0, e1] at h
  exact h

theorem band_0641 : RS5.BandZeros ((16305403216 : ℝ) / 65536) ((16310343240 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0641.s0 RH1E6S02_0641.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0641.s0 RH1E6S02_0641.rest = RH1E6S02_0641.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0641.s0 :: RH1E6S02_0641.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0641.s0.t = ((16305403216 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0641.s0]
  have e1 : RH1E6S02_0641.sL.t = ((16310343240 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0641.sL]
  rw [e0, e1] at h
  exact h

theorem part_080_0 : RS5.BandZeros ((16300456843 : ℝ) / 65536) ((16310343240 : ℝ) / 65536) 254 := by
  have g0 := band_0640
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0641
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((16300456843 : ℝ) / 65536) ((16310343240 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_080_0 <;> assumption
