-- Prove2me | solution 1 for RH1E6S03.part_083_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T08:21:10.568456+00:00
-- url     : https://prove2.me/submissions/d1a3ae09-e67a-4f4b-b3e2-be0ba263db49

import Definitions.Def_RH1E6S03_D083_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0668 : RS5.BandZeros ((19653345029 : ℝ) / 65536) ((19658208704 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0668.s0 RH1E6S03_0668.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0668.s0 RH1E6S03_0668.rest = RH1E6S03_0668.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0668.s0 :: RH1E6S03_0668.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0668.s0.t = ((19653345029 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0668.s0]
  have e1 : RH1E6S03_0668.sL.t = ((19658208704 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0668.sL]
  rw [e0, e1] at h
  exact h

theorem band_0669 : RS5.BandZeros ((19658208704 : ℝ) / 65536) ((19660800000 : ℝ) / 65536) 68 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0669.s0 RH1E6S03_0669.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0669.s0 RH1E6S03_0669.rest = RH1E6S03_0669.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0669.s0 :: RH1E6S03_0669.rest) = 68 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0669.s0.t = ((19658208704 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0669.s0]
  have e1 : RH1E6S03_0669.sL.t = ((19660800000 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0669.sL]
  rw [e0, e1] at h
  exact h

theorem part_083_2 : RS5.BandZeros ((19653345029 : ℝ) / 65536) ((19660800000 : ℝ) / 65536) 195 := by
  have g0 := band_0668
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0669
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((19653345029 : ℝ) / 65536) ((19660800000 : ℝ) / 65536) 195 := by
  apply RH1E6S03.part_083_2 <;> assumption
