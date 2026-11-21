-- Prove2me | solution 1 for RH1E6S06.part_036_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T18:46:22.467247+00:00
-- url     : https://prove2.me/submissions/89637533-2627-4d55-969d-7f95368e7664

import Definitions.Def_RH1E6S06_D036_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0294 : RS5.BandZeros ((27601108998 : ℝ) / 65536) ((27605823075 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0294.s0 RH1E6S06_0294.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0294.s0 RH1E6S06_0294.rest = RH1E6S06_0294.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0294.s0 :: RH1E6S06_0294.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0294.s0.t = ((27601108998 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0294.s0]
  have e1 : RH1E6S06_0294.sL.t = ((27605823075 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0294.sL]
  rw [e0, e1] at h
  exact h

theorem band_0295 : RS5.BandZeros ((27605823075 : ℝ) / 65536) ((27610520520 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0295.s0 RH1E6S06_0295.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0295.s0 RH1E6S06_0295.rest = RH1E6S06_0295.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0295.s0 :: RH1E6S06_0295.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0295.s0.t = ((27605823075 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0295.s0]
  have e1 : RH1E6S06_0295.sL.t = ((27610520520 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0295.sL]
  rw [e0, e1] at h
  exact h

theorem part_036_3 : RS5.BandZeros ((27601108998 : ℝ) / 65536) ((27610520520 : ℝ) / 65536) 254 := by
  have g0 := band_0294
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0295
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((27601108998 : ℝ) / 65536) ((27610520520 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_036_3 <;> assumption
