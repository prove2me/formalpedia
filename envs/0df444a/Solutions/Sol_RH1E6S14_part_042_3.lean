-- Prove2me | solution 1 for RH1E6S14.part_042_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T04:59:06.640643+00:00
-- url     : https://prove2.me/submissions/7a2a93a1-ad86-42ff-9dc3-37c71d3707ec

import Definitions.Def_RH1E6S14_D042_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0342 : RS5.BandZeros ((53948496779 : ℝ) / 65536) ((53952924482 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0342.s0 RH1E6S14_0342.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0342.s0 RH1E6S14_0342.rest = RH1E6S14_0342.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0342.s0 :: RH1E6S14_0342.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0342.s0.t = ((53948496779 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0342.s0]
  have e1 : RH1E6S14_0342.sL.t = ((53952924482 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0342.sL]
  rw [e0, e1] at h
  exact h

theorem band_0343 : RS5.BandZeros ((53952924482 : ℝ) / 65536) ((53957366863 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0343.s0 RH1E6S14_0343.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0343.s0 RH1E6S14_0343.rest = RH1E6S14_0343.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0343.s0 :: RH1E6S14_0343.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0343.s0.t = ((53952924482 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0343.s0]
  have e1 : RH1E6S14_0343.sL.t = ((53957366863 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0343.sL]
  rw [e0, e1] at h
  exact h

theorem part_042_3 : RS5.BandZeros ((53948496779 : ℝ) / 65536) ((53957366863 : ℝ) / 65536) 254 := by
  have g0 := band_0342
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0343
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((53948496779 : ℝ) / 65536) ((53957366863 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_042_3 <;> assumption
