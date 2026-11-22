-- Prove2me | solution 1 for RH1E6S10.part_076_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T02:24:16.635077+00:00
-- url     : https://prove2.me/submissions/17fb852f-201a-4ef5-98bb-b4fef46073bd

import Definitions.Def_RH1E6S10_D076_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0608 : RS5.BandZeros ((42086185499 : ℝ) / 65536) ((42090710278 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0608.s0 RH1E6S10_0608.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0608.s0 RH1E6S10_0608.rest = RH1E6S10_0608.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0608.s0 :: RH1E6S10_0608.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0608.s0.t = ((42086185499 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0608.s0]
  have e1 : RH1E6S10_0608.sL.t = ((42090710278 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0608.sL]
  rw [e0, e1] at h
  exact h

theorem band_0609 : RS5.BandZeros ((42090710278 : ℝ) / 65536) ((42095226091 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0609.s0 RH1E6S10_0609.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0609.s0 RH1E6S10_0609.rest = RH1E6S10_0609.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0609.s0 :: RH1E6S10_0609.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0609.s0.t = ((42090710278 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0609.s0]
  have e1 : RH1E6S10_0609.sL.t = ((42095226091 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0609.sL]
  rw [e0, e1] at h
  exact h

theorem part_076_0 : RS5.BandZeros ((42086185499 : ℝ) / 65536) ((42095226091 : ℝ) / 65536) 254 := by
  have g0 := band_0608
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0609
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((42086185499 : ℝ) / 65536) ((42095226091 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_076_0 <;> assumption
