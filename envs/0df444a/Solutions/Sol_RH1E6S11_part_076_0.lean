-- Prove2me | solution 1 for RH1E6S11.part_076_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T06:38:33.82418+00:00
-- url     : https://prove2.me/submissions/6d0df833-0e56-4787-9458-0d0c80cffb14

import Definitions.Def_RH1E6S11_D076_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0608 : RS5.BandZeros ((45344507988 : ℝ) / 65536) ((45349003706 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0608.s0 RH1E6S11_0608.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0608.s0 RH1E6S11_0608.rest = RH1E6S11_0608.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0608.s0 :: RH1E6S11_0608.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0608.s0.t = ((45344507988 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0608.s0]
  have e1 : RH1E6S11_0608.sL.t = ((45349003706 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0608.sL]
  rw [e0, e1] at h
  exact h

theorem band_0609 : RS5.BandZeros ((45349003706 : ℝ) / 65536) ((45353517119 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0609.s0 RH1E6S11_0609.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0609.s0 RH1E6S11_0609.rest = RH1E6S11_0609.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0609.s0 :: RH1E6S11_0609.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0609.s0.t = ((45349003706 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0609.s0]
  have e1 : RH1E6S11_0609.sL.t = ((45353517119 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0609.sL]
  rw [e0, e1] at h
  exact h

theorem part_076_0 : RS5.BandZeros ((45344507988 : ℝ) / 65536) ((45353517119 : ℝ) / 65536) 254 := by
  have g0 := band_0608
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0609
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((45344507988 : ℝ) / 65536) ((45353517119 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_076_0 <;> assumption
