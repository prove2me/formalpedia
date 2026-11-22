-- Prove2me | solution 1 for RH1E6S11.part_025_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T04:11:20.674296+00:00
-- url     : https://prove2.me/submissions/d039d42f-6538-45bd-9163-23107a19b8f4

import Definitions.Def_RH1E6S11_D025_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0202 : RS5.BandZeros ((43512406758 : ℝ) / 65536) ((43516918503 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0202.s0 RH1E6S11_0202.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0202.s0 RH1E6S11_0202.rest = RH1E6S11_0202.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0202.s0 :: RH1E6S11_0202.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0202.s0.t = ((43512406758 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0202.s0]
  have e1 : RH1E6S11_0202.sL.t = ((43516918503 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0202.sL]
  rw [e0, e1] at h
  exact h

theorem band_0203 : RS5.BandZeros ((43516918503 : ℝ) / 65536) ((43521448005 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0203.s0 RH1E6S11_0203.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0203.s0 RH1E6S11_0203.rest = RH1E6S11_0203.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0203.s0 :: RH1E6S11_0203.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0203.s0.t = ((43516918503 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0203.s0]
  have e1 : RH1E6S11_0203.sL.t = ((43521448005 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0203.sL]
  rw [e0, e1] at h
  exact h

theorem part_025_1 : RS5.BandZeros ((43512406758 : ℝ) / 65536) ((43521448005 : ℝ) / 65536) 254 := by
  have g0 := band_0202
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0203
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((43512406758 : ℝ) / 65536) ((43521448005 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_025_1 <;> assumption
