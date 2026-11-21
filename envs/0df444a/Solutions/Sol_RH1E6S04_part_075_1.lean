-- Prove2me | solution 1 for RH1E6S04.part_075_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T11:13:14.305367+00:00
-- url     : https://prove2.me/submissions/b9653050-279d-456e-993c-369f2367abf8

import Definitions.Def_RH1E6S04_D075_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0602 : RS5.BandZeros ((22563946135 : ℝ) / 65536) ((22568738824 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0602.s0 RH1E6S04_0602.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0602.s0 RH1E6S04_0602.rest = RH1E6S04_0602.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0602.s0 :: RH1E6S04_0602.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0602.s0.t = ((22563946135 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0602.s0]
  have e1 : RH1E6S04_0602.sL.t = ((22568738824 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0602.sL]
  rw [e0, e1] at h
  exact h

theorem band_0603 : RS5.BandZeros ((22568738824 : ℝ) / 65536) ((22573521987 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0603.s0 RH1E6S04_0603.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0603.s0 RH1E6S04_0603.rest = RH1E6S04_0603.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0603.s0 :: RH1E6S04_0603.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0603.s0.t = ((22568738824 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0603.s0]
  have e1 : RH1E6S04_0603.sL.t = ((22573521987 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0603.sL]
  rw [e0, e1] at h
  exact h

theorem part_075_1 : RS5.BandZeros ((22563946135 : ℝ) / 65536) ((22573521987 : ℝ) / 65536) 254 := by
  have g0 := band_0602
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0603
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((22563946135 : ℝ) / 65536) ((22573521987 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_075_1 <;> assumption
