-- Prove2me | solution 1 for RH1E6S11.part_080_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T06:50:07.563476+00:00
-- url     : https://prove2.me/submissions/bf5c8a73-4fa3-44ea-b42e-566340e28cae

import Definitions.Def_RH1E6S11_D080_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0640 : RS5.BandZeros ((45488635610 : ℝ) / 65536) ((45493147828 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0640.s0 RH1E6S11_0640.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0640.s0 RH1E6S11_0640.rest = RH1E6S11_0640.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0640.s0 :: RH1E6S11_0640.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0640.s0.t = ((45488635610 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0640.s0]
  have e1 : RH1E6S11_0640.sL.t = ((45493147828 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0640.sL]
  rw [e0, e1] at h
  exact h

theorem band_0641 : RS5.BandZeros ((45493147828 : ℝ) / 65536) ((45497642279 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0641.s0 RH1E6S11_0641.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0641.s0 RH1E6S11_0641.rest = RH1E6S11_0641.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0641.s0 :: RH1E6S11_0641.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0641.s0.t = ((45493147828 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0641.s0]
  have e1 : RH1E6S11_0641.sL.t = ((45497642279 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0641.sL]
  rw [e0, e1] at h
  exact h

theorem part_080_0 : RS5.BandZeros ((45488635610 : ℝ) / 65536) ((45497642279 : ℝ) / 65536) 254 := by
  have g0 := band_0640
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0641
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((45488635610 : ℝ) / 65536) ((45497642279 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_080_0 <;> assumption
