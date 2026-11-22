-- Prove2me | solution 1 for RH1E6S12.part_015_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T08:11:25.631349+00:00
-- url     : https://prove2.me/submissions/1e6bea5e-ceeb-4116-b8e0-ff48b02cde94

import Definitions.Def_RH1E6S12_D015_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0126 : RS5.BandZeros ((46441929104 : ℝ) / 65536) ((46446424430 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0126.s0 RH1E6S12_0126.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0126.s0 RH1E6S12_0126.rest = RH1E6S12_0126.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0126.s0 :: RH1E6S12_0126.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0126.s0.t = ((46441929104 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0126.s0]
  have e1 : RH1E6S12_0126.sL.t = ((46446424430 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0126.sL]
  rw [e0, e1] at h
  exact h

theorem band_0127 : RS5.BandZeros ((46446424430 : ℝ) / 65536) ((46450928567 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0127.s0 RH1E6S12_0127.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0127.s0 RH1E6S12_0127.rest = RH1E6S12_0127.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0127.s0 :: RH1E6S12_0127.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0127.s0.t = ((46446424430 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0127.s0]
  have e1 : RH1E6S12_0127.sL.t = ((46450928567 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0127.sL]
  rw [e0, e1] at h
  exact h

theorem part_015_3 : RS5.BandZeros ((46441929104 : ℝ) / 65536) ((46450928567 : ℝ) / 65536) 254 := by
  have g0 := band_0126
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0127
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((46441929104 : ℝ) / 65536) ((46450928567 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_015_3 <;> assumption
