-- Prove2me | solution 1 for RH1E6S12.part_070_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T16:41:30.172093+00:00
-- url     : https://prove2.me/submissions/d67c8f7d-1fda-432c-892d-b91f2699dda5

import Definitions.Def_RH1E6S12_D070_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0560 : RS5.BandZeros ((48389440989 : ℝ) / 65536) ((48393933393 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0560.s0 RH1E6S12_0560.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0560.s0 RH1E6S12_0560.rest = RH1E6S12_0560.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0560.s0 :: RH1E6S12_0560.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0560.s0.t = ((48389440989 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0560.s0]
  have e1 : RH1E6S12_0560.sL.t = ((48393933393 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0560.sL]
  rw [e0, e1] at h
  exact h

theorem band_0561 : RS5.BandZeros ((48393933393 : ℝ) / 65536) ((48398389815 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0561.s0 RH1E6S12_0561.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0561.s0 RH1E6S12_0561.rest = RH1E6S12_0561.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0561.s0 :: RH1E6S12_0561.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0561.s0.t = ((48393933393 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0561.s0]
  have e1 : RH1E6S12_0561.sL.t = ((48398389815 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0561.sL]
  rw [e0, e1] at h
  exact h

theorem part_070_0 : RS5.BandZeros ((48389440989 : ℝ) / 65536) ((48398389815 : ℝ) / 65536) 254 := by
  have g0 := band_0560
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0561
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((48389440989 : ℝ) / 65536) ((48398389815 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_070_0 <;> assumption
