-- Prove2me | solution 1 for RH1E6S02.part_069_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T04:35:30.777225+00:00
-- url     : https://prove2.me/submissions/83814dbf-757c-431c-b090-f27dee8c777e

import Definitions.Def_RH1E6S02_D069_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0554 : RS5.BandZeros ((15875089680 : ℝ) / 65536) ((15880045157 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0554.s0 RH1E6S02_0554.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0554.s0 RH1E6S02_0554.rest = RH1E6S02_0554.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0554.s0 :: RH1E6S02_0554.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0554.s0.t = ((15875089680 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0554.s0]
  have e1 : RH1E6S02_0554.sL.t = ((15880045157 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0554.sL]
  rw [e0, e1] at h
  exact h

theorem band_0555 : RS5.BandZeros ((15880045157 : ℝ) / 65536) ((15885013518 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0555.s0 RH1E6S02_0555.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0555.s0 RH1E6S02_0555.rest = RH1E6S02_0555.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0555.s0 :: RH1E6S02_0555.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0555.s0.t = ((15880045157 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0555.s0]
  have e1 : RH1E6S02_0555.sL.t = ((15885013518 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0555.sL]
  rw [e0, e1] at h
  exact h

theorem part_069_1 : RS5.BandZeros ((15875089680 : ℝ) / 65536) ((15885013518 : ℝ) / 65536) 254 := by
  have g0 := band_0554
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0555
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((15875089680 : ℝ) / 65536) ((15885013518 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_069_1 <;> assumption
