-- Prove2me | solution 1 for RH1E6S10.part_009_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T17:50:08.136644+00:00
-- url     : https://prove2.me/submissions/e9101f96-71ad-453e-9619-7934a4b2ebc1

import Definitions.Def_RH1E6S10_D009_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0074 : RS5.BandZeros ((39658961319 : ℝ) / 65536) ((39663545402 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0074.s0 RH1E6S10_0074.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0074.s0 RH1E6S10_0074.rest = RH1E6S10_0074.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0074.s0 :: RH1E6S10_0074.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0074.s0.t = ((39658961319 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0074.s0]
  have e1 : RH1E6S10_0074.sL.t = ((39663545402 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0074.sL]
  rw [e0, e1] at h
  exact h

theorem band_0075 : RS5.BandZeros ((39663545402 : ℝ) / 65536) ((39668093557 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0075.s0 RH1E6S10_0075.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0075.s0 RH1E6S10_0075.rest = RH1E6S10_0075.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0075.s0 :: RH1E6S10_0075.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0075.s0.t = ((39663545402 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0075.s0]
  have e1 : RH1E6S10_0075.sL.t = ((39668093557 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0075.sL]
  rw [e0, e1] at h
  exact h

theorem part_009_1 : RS5.BandZeros ((39658961319 : ℝ) / 65536) ((39668093557 : ℝ) / 65536) 254 := by
  have g0 := band_0074
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0075
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((39658961319 : ℝ) / 65536) ((39668093557 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_009_1 <;> assumption
