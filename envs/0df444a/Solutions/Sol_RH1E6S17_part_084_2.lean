-- Prove2me | solution 1 for RH1E6S17.part_084_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T00:18:17.000688+00:00
-- url     : https://prove2.me/submissions/6606f85b-9072-4dbe-bd64-38f892d59758

import Definitions.Def_RH1E6S17_D084_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0676 : RS5.BandZeros ((65217562954 : ℝ) / 65536) ((65221948003 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0676.s0 RH1E6S17_0676.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0676.s0 RH1E6S17_0676.rest = RH1E6S17_0676.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0676.s0 :: RH1E6S17_0676.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0676.s0.t = ((65217562954 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0676.s0]
  have e1 : RH1E6S17_0676.sL.t = ((65221948003 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0676.sL]
  rw [e0, e1] at h
  exact h

theorem band_0677 : RS5.BandZeros ((65221948003 : ℝ) / 65536) ((65226315830 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0677.s0 RH1E6S17_0677.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0677.s0 RH1E6S17_0677.rest = RH1E6S17_0677.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0677.s0 :: RH1E6S17_0677.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0677.s0.t = ((65221948003 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0677.s0]
  have e1 : RH1E6S17_0677.sL.t = ((65226315830 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0677.sL]
  rw [e0, e1] at h
  exact h

theorem part_084_2 : RS5.BandZeros ((65217562954 : ℝ) / 65536) ((65226315830 : ℝ) / 65536) 254 := by
  have g0 := band_0676
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0677
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((65217562954 : ℝ) / 65536) ((65226315830 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_084_2 <;> assumption
