-- Prove2me | solution 1 for RH1E6S11.part_087_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T07:10:19.727347+00:00
-- url     : https://prove2.me/submissions/fc89f431-f706-466a-b8f5-1c45416022b4

import Definitions.Def_RH1E6S11_D087_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0698 : RS5.BandZeros ((45749775687 : ℝ) / 65536) ((45754259102 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0698.s0 RH1E6S11_0698.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0698.s0 RH1E6S11_0698.rest = RH1E6S11_0698.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0698.s0 :: RH1E6S11_0698.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0698.s0.t = ((45749775687 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0698.s0]
  have e1 : RH1E6S11_0698.sL.t = ((45754259102 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0698.sL]
  rw [e0, e1] at h
  exact h

theorem band_0699 : RS5.BandZeros ((45754259102 : ℝ) / 65536) ((45758769059 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0699.s0 RH1E6S11_0699.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0699.s0 RH1E6S11_0699.rest = RH1E6S11_0699.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0699.s0 :: RH1E6S11_0699.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0699.s0.t = ((45754259102 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0699.s0]
  have e1 : RH1E6S11_0699.sL.t = ((45758769059 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0699.sL]
  rw [e0, e1] at h
  exact h

theorem part_087_1 : RS5.BandZeros ((45749775687 : ℝ) / 65536) ((45758769059 : ℝ) / 65536) 254 := by
  have g0 := band_0698
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0699
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((45749775687 : ℝ) / 65536) ((45758769059 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_087_1 <;> assumption
