-- Prove2me | solution 1 for RH1E6S08.part_009_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T04:22:56.787485+00:00
-- url     : https://prove2.me/submissions/86dc6327-8176-4cc2-b055-bf8b634ed463

import Definitions.Def_RH1E6S08_D009_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0074 : RS5.BandZeros ((33110794669 : ℝ) / 65536) ((33115428731 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0074.s0 RH1E6S08_0074.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0074.s0 RH1E6S08_0074.rest = RH1E6S08_0074.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0074.s0 :: RH1E6S08_0074.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0074.s0.t = ((33110794669 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0074.s0]
  have e1 : RH1E6S08_0074.sL.t = ((33115428731 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0074.sL]
  rw [e0, e1] at h
  exact h

theorem band_0075 : RS5.BandZeros ((33115428731 : ℝ) / 65536) ((33120072790 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0075.s0 RH1E6S08_0075.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0075.s0 RH1E6S08_0075.rest = RH1E6S08_0075.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0075.s0 :: RH1E6S08_0075.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0075.s0.t = ((33115428731 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0075.s0]
  have e1 : RH1E6S08_0075.sL.t = ((33120072790 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0075.sL]
  rw [e0, e1] at h
  exact h

theorem part_009_1 : RS5.BandZeros ((33110794669 : ℝ) / 65536) ((33120072790 : ℝ) / 65536) 254 := by
  have g0 := band_0074
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0075
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((33110794669 : ℝ) / 65536) ((33120072790 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_009_1 <;> assumption
