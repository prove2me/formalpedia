-- Prove2me | solution 1 for RH1E6S02.part_045_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T03:44:22.638918+00:00
-- url     : https://prove2.me/submissions/dc79e8fc-5fd5-4ef8-9c73-ceff08a1da98

import Definitions.Def_RH1E6S02_D045_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0366 : RS5.BandZeros ((14941425473 : ℝ) / 65536) ((14946385575 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0366.s0 RH1E6S02_0366.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0366.s0 RH1E6S02_0366.rest = RH1E6S02_0366.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0366.s0 :: RH1E6S02_0366.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0366.s0.t = ((14941425473 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0366.s0]
  have e1 : RH1E6S02_0366.sL.t = ((14946385575 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0366.sL]
  rw [e0, e1] at h
  exact h

theorem band_0367 : RS5.BandZeros ((14946385575 : ℝ) / 65536) ((14951375148 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0367.s0 RH1E6S02_0367.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0367.s0 RH1E6S02_0367.rest = RH1E6S02_0367.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0367.s0 :: RH1E6S02_0367.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0367.s0.t = ((14946385575 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0367.s0]
  have e1 : RH1E6S02_0367.sL.t = ((14951375148 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0367.sL]
  rw [e0, e1] at h
  exact h

theorem part_045_3 : RS5.BandZeros ((14941425473 : ℝ) / 65536) ((14951375148 : ℝ) / 65536) 254 := by
  have g0 := band_0366
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0367
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((14941425473 : ℝ) / 65536) ((14951375148 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_045_3 <;> assumption
