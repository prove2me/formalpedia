-- Prove2me | solution 1 for RH1E6S11.part_025_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T04:11:18.079983+00:00
-- url     : https://prove2.me/submissions/34f35cd7-1b7b-4258-9ec8-1a3cd1aa9c5b

import Definitions.Def_RH1E6S11_D025_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0200 : RS5.BandZeros ((43503356450 : ℝ) / 65536) ((43507886074 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0200.s0 RH1E6S11_0200.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0200.s0 RH1E6S11_0200.rest = RH1E6S11_0200.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0200.s0 :: RH1E6S11_0200.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0200.s0.t = ((43503356450 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0200.s0]
  have e1 : RH1E6S11_0200.sL.t = ((43507886074 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0200.sL]
  rw [e0, e1] at h
  exact h

theorem band_0201 : RS5.BandZeros ((43507886074 : ℝ) / 65536) ((43512406758 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0201.s0 RH1E6S11_0201.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0201.s0 RH1E6S11_0201.rest = RH1E6S11_0201.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0201.s0 :: RH1E6S11_0201.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0201.s0.t = ((43507886074 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0201.s0]
  have e1 : RH1E6S11_0201.sL.t = ((43512406758 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0201.sL]
  rw [e0, e1] at h
  exact h

theorem part_025_0 : RS5.BandZeros ((43503356450 : ℝ) / 65536) ((43512406758 : ℝ) / 65536) 254 := by
  have g0 := band_0200
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0201
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((43503356450 : ℝ) / 65536) ((43512406758 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_025_0 <;> assumption
