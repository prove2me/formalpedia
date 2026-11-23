-- Prove2me | solution 1 for RH1E6S14.part_007_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T02:51:33.471825+00:00
-- url     : https://prove2.me/submissions/52583735-ccd1-49f0-b3e1-1dede5a850f4

import Definitions.Def_RH1E6S14_D007_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0062 : RS5.BandZeros ((52704573029 : ℝ) / 65536) ((52709028242 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0062.s0 RH1E6S14_0062.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0062.s0 RH1E6S14_0062.rest = RH1E6S14_0062.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0062.s0 :: RH1E6S14_0062.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0062.s0.t = ((52704573029 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0062.s0]
  have e1 : RH1E6S14_0062.sL.t = ((52709028242 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0062.sL]
  rw [e0, e1] at h
  exact h

theorem band_0063 : RS5.BandZeros ((52709028242 : ℝ) / 65536) ((52713475182 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0063.s0 RH1E6S14_0063.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0063.s0 RH1E6S14_0063.rest = RH1E6S14_0063.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0063.s0 :: RH1E6S14_0063.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0063.s0.t = ((52709028242 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0063.s0]
  have e1 : RH1E6S14_0063.sL.t = ((52713475182 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0063.sL]
  rw [e0, e1] at h
  exact h

theorem part_007_3 : RS5.BandZeros ((52704573029 : ℝ) / 65536) ((52713475182 : ℝ) / 65536) 254 := by
  have g0 := band_0062
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0063
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((52704573029 : ℝ) / 65536) ((52713475182 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_007_3 <;> assumption
