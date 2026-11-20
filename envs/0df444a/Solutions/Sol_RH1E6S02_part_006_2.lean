-- Prove2me | solution 1 for RH1E6S02.part_006_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T02:22:32.462317+00:00
-- url     : https://prove2.me/submissions/72a66202-35ef-4fdb-927c-200c79eca2f0

import Definitions.Def_RH1E6S02_D006_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0052 : RS5.BandZeros ((13369236009 : ℝ) / 65536) ((13374280045 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0052.s0 RH1E6S02_0052.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0052.s0 RH1E6S02_0052.rest = RH1E6S02_0052.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0052.s0 :: RH1E6S02_0052.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0052.s0.t = ((13369236009 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0052.s0]
  have e1 : RH1E6S02_0052.sL.t = ((13374280045 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0052.sL]
  rw [e0, e1] at h
  exact h

theorem band_0053 : RS5.BandZeros ((13374280045 : ℝ) / 65536) ((13379294751 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0053.s0 RH1E6S02_0053.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0053.s0 RH1E6S02_0053.rest = RH1E6S02_0053.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0053.s0 :: RH1E6S02_0053.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0053.s0.t = ((13374280045 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0053.s0]
  have e1 : RH1E6S02_0053.sL.t = ((13379294751 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0053.sL]
  rw [e0, e1] at h
  exact h

theorem part_006_2 : RS5.BandZeros ((13369236009 : ℝ) / 65536) ((13379294751 : ℝ) / 65536) 254 := by
  have g0 := band_0052
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0053
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((13369236009 : ℝ) / 65536) ((13379294751 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_006_2 <;> assumption
