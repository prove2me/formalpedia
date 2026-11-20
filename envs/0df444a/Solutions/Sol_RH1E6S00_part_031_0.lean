-- Prove2me | solution 1 for RH1E6S00.part_031_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T21:49:28.515908+00:00
-- url     : https://prove2.me/submissions/debea3aa-0fc4-4821-b603-90caf2423a93

import Definitions.Def_RH1E6S00_D031_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0248 : RS5.BandZeros ((7881072193 : ℝ) / 65536) ((7886376075 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0248.s0 RH1E6S00_0248.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0248.s0 RH1E6S00_0248.rest = RH1E6S00_0248.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0248.s0 :: RH1E6S00_0248.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0248.s0.t = ((7881072193 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0248.s0]
  have e1 : RH1E6S00_0248.sL.t = ((7886376075 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0248.sL]
  rw [e0, e1] at h
  exact h

theorem band_0249 : RS5.BandZeros ((7886376075 : ℝ) / 65536) ((7891669157 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0249.s0 RH1E6S00_0249.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0249.s0 RH1E6S00_0249.rest = RH1E6S00_0249.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0249.s0 :: RH1E6S00_0249.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0249.s0.t = ((7886376075 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0249.s0]
  have e1 : RH1E6S00_0249.sL.t = ((7891669157 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0249.sL]
  rw [e0, e1] at h
  exact h

theorem part_031_0 : RS5.BandZeros ((7881072193 : ℝ) / 65536) ((7891669157 : ℝ) / 65536) 254 := by
  have g0 := band_0248
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0249
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((7881072193 : ℝ) / 65536) ((7891669157 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_031_0 <;> assumption
