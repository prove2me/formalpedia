-- Prove2me | solution 1 for RH1E6S14.part_014_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T03:15:16.020743+00:00
-- url     : https://prove2.me/submissions/b54b4ce3-d3a4-42e8-bdff-96254148f2fe

import Definitions.Def_RH1E6S14_D014_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0118 : RS5.BandZeros ((52953550170 : ℝ) / 65536) ((52958004670 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0118.s0 RH1E6S14_0118.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0118.s0 RH1E6S14_0118.rest = RH1E6S14_0118.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0118.s0 :: RH1E6S14_0118.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0118.s0.t = ((52953550170 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0118.s0]
  have e1 : RH1E6S14_0118.sL.t = ((52958004670 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0118.sL]
  rw [e0, e1] at h
  exact h

theorem band_0119 : RS5.BandZeros ((52958004670 : ℝ) / 65536) ((52962438208 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0119.s0 RH1E6S14_0119.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0119.s0 RH1E6S14_0119.rest = RH1E6S14_0119.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0119.s0 :: RH1E6S14_0119.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0119.s0.t = ((52958004670 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0119.s0]
  have e1 : RH1E6S14_0119.sL.t = ((52962438208 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0119.sL]
  rw [e0, e1] at h
  exact h

theorem part_014_3 : RS5.BandZeros ((52953550170 : ℝ) / 65536) ((52962438208 : ℝ) / 65536) 254 := by
  have g0 := band_0118
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0119
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((52953550170 : ℝ) / 65536) ((52962438208 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_014_3 <;> assumption
