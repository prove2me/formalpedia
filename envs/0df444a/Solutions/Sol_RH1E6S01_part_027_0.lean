-- Prove2me | solution 1 for RH1E6S01.part_027_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T00:19:45.110973+00:00
-- url     : https://prove2.me/submissions/ef187786-0037-4dc9-b3d0-6e9e26268fbd

import Definitions.Def_RH1E6S01_D027_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0216 : RS5.BandZeros ((10944898735 : ℝ) / 65536) ((10950041807 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0216.s0 RH1E6S01_0216.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0216.s0 RH1E6S01_0216.rest = RH1E6S01_0216.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0216.s0 :: RH1E6S01_0216.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0216.s0.t = ((10944898735 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0216.s0]
  have e1 : RH1E6S01_0216.sL.t = ((10950041807 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0216.sL]
  rw [e0, e1] at h
  exact h

theorem band_0217 : RS5.BandZeros ((10950041807 : ℝ) / 65536) ((10955174538 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0217.s0 RH1E6S01_0217.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0217.s0 RH1E6S01_0217.rest = RH1E6S01_0217.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0217.s0 :: RH1E6S01_0217.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0217.s0.t = ((10950041807 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0217.s0]
  have e1 : RH1E6S01_0217.sL.t = ((10955174538 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0217.sL]
  rw [e0, e1] at h
  exact h

theorem part_027_0 : RS5.BandZeros ((10944898735 : ℝ) / 65536) ((10955174538 : ℝ) / 65536) 254 := by
  have g0 := band_0216
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0217
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((10944898735 : ℝ) / 65536) ((10955174538 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_027_0 <;> assumption
