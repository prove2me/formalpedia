-- Prove2me | solution 1 for RH1E6S14.part_023_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T03:52:43.370357+00:00
-- url     : https://prove2.me/submissions/913988ec-2eb2-4fbb-b479-29289053813f

import Definitions.Def_RH1E6S14_D023_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0186 : RS5.BandZeros ((53255761565 : ℝ) / 65536) ((53260183021 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0186.s0 RH1E6S14_0186.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0186.s0 RH1E6S14_0186.rest = RH1E6S14_0186.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0186.s0 :: RH1E6S14_0186.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0186.s0.t = ((53255761565 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0186.s0]
  have e1 : RH1E6S14_0186.sL.t = ((53260183021 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0186.sL]
  rw [e0, e1] at h
  exact h

theorem band_0187 : RS5.BandZeros ((53260183021 : ℝ) / 65536) ((53264640829 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0187.s0 RH1E6S14_0187.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0187.s0 RH1E6S14_0187.rest = RH1E6S14_0187.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0187.s0 :: RH1E6S14_0187.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0187.s0.t = ((53260183021 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0187.s0]
  have e1 : RH1E6S14_0187.sL.t = ((53264640829 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0187.sL]
  rw [e0, e1] at h
  exact h

theorem part_023_1 : RS5.BandZeros ((53255761565 : ℝ) / 65536) ((53264640829 : ℝ) / 65536) 254 := by
  have g0 := band_0186
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0187
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((53255761565 : ℝ) / 65536) ((53264640829 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_023_1 <;> assumption
