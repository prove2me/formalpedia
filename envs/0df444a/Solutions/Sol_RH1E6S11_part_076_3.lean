-- Prove2me | solution 1 for RH1E6S11.part_076_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T06:41:24.075407+00:00
-- url     : https://prove2.me/submissions/56525033-41b7-46ad-b4e8-4648f3e660d7

import Definitions.Def_RH1E6S11_D076_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0614 : RS5.BandZeros ((45371517185 : ℝ) / 65536) ((45376048139 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0614.s0 RH1E6S11_0614.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0614.s0 RH1E6S11_0614.rest = RH1E6S11_0614.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0614.s0 :: RH1E6S11_0614.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0614.s0.t = ((45371517185 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0614.s0]
  have e1 : RH1E6S11_0614.sL.t = ((45376048139 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0614.sL]
  rw [e0, e1] at h
  exact h

theorem band_0615 : RS5.BandZeros ((45376048139 : ℝ) / 65536) ((45380534721 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0615.s0 RH1E6S11_0615.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0615.s0 RH1E6S11_0615.rest = RH1E6S11_0615.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0615.s0 :: RH1E6S11_0615.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0615.s0.t = ((45376048139 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0615.s0]
  have e1 : RH1E6S11_0615.sL.t = ((45380534721 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0615.sL]
  rw [e0, e1] at h
  exact h

theorem part_076_3 : RS5.BandZeros ((45371517185 : ℝ) / 65536) ((45380534721 : ℝ) / 65536) 254 := by
  have g0 := band_0614
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0615
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((45371517185 : ℝ) / 65536) ((45380534721 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_076_3 <;> assumption
