-- Prove2me | solution 1 for RH1E6S12.part_009_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T07:53:52.869478+00:00
-- url     : https://prove2.me/submissions/8c6035fb-4593-4660-b1ca-88f42fca17e9

import Definitions.Def_RH1E6S12_D009_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0074 : RS5.BandZeros ((46208111671 : ℝ) / 65536) ((46212609029 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0074.s0 RH1E6S12_0074.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0074.s0 RH1E6S12_0074.rest = RH1E6S12_0074.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0074.s0 :: RH1E6S12_0074.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0074.s0.t = ((46208111671 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0074.s0]
  have e1 : RH1E6S12_0074.sL.t = ((46212609029 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0074.sL]
  rw [e0, e1] at h
  exact h

theorem band_0075 : RS5.BandZeros ((46212609029 : ℝ) / 65536) ((46217109457 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0075.s0 RH1E6S12_0075.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0075.s0 RH1E6S12_0075.rest = RH1E6S12_0075.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0075.s0 :: RH1E6S12_0075.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0075.s0.t = ((46212609029 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0075.s0]
  have e1 : RH1E6S12_0075.sL.t = ((46217109457 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0075.sL]
  rw [e0, e1] at h
  exact h

theorem part_009_1 : RS5.BandZeros ((46208111671 : ℝ) / 65536) ((46217109457 : ℝ) / 65536) 254 := by
  have g0 := band_0074
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0075
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((46208111671 : ℝ) / 65536) ((46217109457 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_009_1 <;> assumption
