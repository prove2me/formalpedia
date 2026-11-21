-- Prove2me | solution 1 for RH1E6S05.part_084_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T17:07:39.53045+00:00
-- url     : https://prove2.me/submissions/6e73276f-283e-414d-b209-bbbe712b79db

import Definitions.Def_RH1E6S05_D084_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0676 : RS5.BandZeros ((26152882345 : ℝ) / 65536) ((26157638999 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0676.s0 RH1E6S05_0676.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0676.s0 RH1E6S05_0676.rest = RH1E6S05_0676.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0676.s0 :: RH1E6S05_0676.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0676.s0.t = ((26152882345 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0676.s0]
  have e1 : RH1E6S05_0676.sL.t = ((26157638999 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0676.sL]
  rw [e0, e1] at h
  exact h

theorem band_0677 : RS5.BandZeros ((26157638999 : ℝ) / 65536) ((26162349033 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0677.s0 RH1E6S05_0677.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0677.s0 RH1E6S05_0677.rest = RH1E6S05_0677.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0677.s0 :: RH1E6S05_0677.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0677.s0.t = ((26157638999 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0677.s0]
  have e1 : RH1E6S05_0677.sL.t = ((26162349033 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0677.sL]
  rw [e0, e1] at h
  exact h

theorem part_084_2 : RS5.BandZeros ((26152882345 : ℝ) / 65536) ((26162349033 : ℝ) / 65536) 254 := by
  have g0 := band_0676
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0677
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((26152882345 : ℝ) / 65536) ((26162349033 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_084_2 <;> assumption
