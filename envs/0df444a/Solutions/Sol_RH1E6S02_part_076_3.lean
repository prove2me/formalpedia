-- Prove2me | solution 1 for RH1E6S02.part_076_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T04:52:23.164218+00:00
-- url     : https://prove2.me/submissions/890d6c57-9b2c-4a7b-9f7c-a3f9cbbd1031

import Definitions.Def_RH1E6S02_D076_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0614 : RS5.BandZeros ((16171967537 : ℝ) / 65536) ((16176911020 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0614.s0 RH1E6S02_0614.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0614.s0 RH1E6S02_0614.rest = RH1E6S02_0614.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0614.s0 :: RH1E6S02_0614.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0614.s0.t = ((16171967537 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0614.s0]
  have e1 : RH1E6S02_0614.sL.t = ((16176911020 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0614.sL]
  rw [e0, e1] at h
  exact h

theorem band_0615 : RS5.BandZeros ((16176911020 : ℝ) / 65536) ((16181891806 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0615.s0 RH1E6S02_0615.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0615.s0 RH1E6S02_0615.rest = RH1E6S02_0615.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0615.s0 :: RH1E6S02_0615.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0615.s0.t = ((16176911020 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0615.s0]
  have e1 : RH1E6S02_0615.sL.t = ((16181891806 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0615.sL]
  rw [e0, e1] at h
  exact h

theorem part_076_3 : RS5.BandZeros ((16171967537 : ℝ) / 65536) ((16181891806 : ℝ) / 65536) 254 := by
  have g0 := band_0614
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0615
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((16171967537 : ℝ) / 65536) ((16181891806 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_076_3 <;> assumption
