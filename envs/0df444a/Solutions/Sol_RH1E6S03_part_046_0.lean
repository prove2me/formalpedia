-- Prove2me | solution 1 for RH1E6S03.part_046_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T06:57:25.851926+00:00
-- url     : https://prove2.me/submissions/1f865c89-d93b-4afc-8f65-5ee157087978

import Definitions.Def_RH1E6S03_D046_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0368 : RS5.BandZeros ((18191909153 : ℝ) / 65536) ((18196817584 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0368.s0 RH1E6S03_0368.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0368.s0 RH1E6S03_0368.rest = RH1E6S03_0368.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0368.s0 :: RH1E6S03_0368.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0368.s0.t = ((18191909153 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0368.s0]
  have e1 : RH1E6S03_0368.sL.t = ((18196817584 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0368.sL]
  rw [e0, e1] at h
  exact h

theorem band_0369 : RS5.BandZeros ((18196817584 : ℝ) / 65536) ((18201725891 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0369.s0 RH1E6S03_0369.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0369.s0 RH1E6S03_0369.rest = RH1E6S03_0369.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0369.s0 :: RH1E6S03_0369.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0369.s0.t = ((18196817584 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0369.s0]
  have e1 : RH1E6S03_0369.sL.t = ((18201725891 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0369.sL]
  rw [e0, e1] at h
  exact h

theorem part_046_0 : RS5.BandZeros ((18191909153 : ℝ) / 65536) ((18201725891 : ℝ) / 65536) 254 := by
  have g0 := band_0368
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0369
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((18191909153 : ℝ) / 65536) ((18201725891 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_046_0 <;> assumption
