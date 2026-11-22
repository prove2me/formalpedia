-- Prove2me | solution 1 for RH1E6S10.part_043_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T00:52:12.007052+00:00
-- url     : https://prove2.me/submissions/39f17ac8-b47f-4c2b-82fd-9419b7194063

import Definitions.Def_RH1E6S10_D043_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0344 : RS5.BandZeros ((40887788583 : ℝ) / 65536) ((40892324722 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0344.s0 RH1E6S10_0344.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0344.s0 RH1E6S10_0344.rest = RH1E6S10_0344.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0344.s0 :: RH1E6S10_0344.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0344.s0.t = ((40887788583 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0344.s0]
  have e1 : RH1E6S10_0344.sL.t = ((40892324722 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0344.sL]
  rw [e0, e1] at h
  exact h

theorem band_0345 : RS5.BandZeros ((40892324722 : ℝ) / 65536) ((40896869764 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0345.s0 RH1E6S10_0345.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0345.s0 RH1E6S10_0345.rest = RH1E6S10_0345.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0345.s0 :: RH1E6S10_0345.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0345.s0.t = ((40892324722 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0345.s0]
  have e1 : RH1E6S10_0345.sL.t = ((40896869764 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0345.sL]
  rw [e0, e1] at h
  exact h

theorem part_043_0 : RS5.BandZeros ((40887788583 : ℝ) / 65536) ((40896869764 : ℝ) / 65536) 254 := by
  have g0 := band_0344
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0345
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((40887788583 : ℝ) / 65536) ((40896869764 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_043_0 <;> assumption
