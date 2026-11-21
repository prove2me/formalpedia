-- Prove2me | solution 1 for RH1E6S06.part_000_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T17:14:59.52261+00:00
-- url     : https://prove2.me/submissions/f8e8aecb-f15a-4d4b-8434-731de22b490f

import Definitions.Def_RH1E6S06_D000_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0004 : RS5.BandZeros ((26233316065 : ℝ) / 65536) ((26238034506 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0004.s0 RH1E6S06_0004.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0004.s0 RH1E6S06_0004.rest = RH1E6S06_0004.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0004.s0 :: RH1E6S06_0004.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0004.s0.t = ((26233316065 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0004.s0]
  have e1 : RH1E6S06_0004.sL.t = ((26238034506 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0004.sL]
  rw [e0, e1] at h
  exact h

theorem band_0005 : RS5.BandZeros ((26238034506 : ℝ) / 65536) ((26242755179 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0005.s0 RH1E6S06_0005.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0005.s0 RH1E6S06_0005.rest = RH1E6S06_0005.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0005.s0 :: RH1E6S06_0005.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0005.s0.t = ((26238034506 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0005.s0]
  have e1 : RH1E6S06_0005.sL.t = ((26242755179 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0005.sL]
  rw [e0, e1] at h
  exact h

theorem part_000_2 : RS5.BandZeros ((26233316065 : ℝ) / 65536) ((26242755179 : ℝ) / 65536) 254 := by
  have g0 := band_0004
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0005
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((26233316065 : ℝ) / 65536) ((26242755179 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_000_2 <;> assumption
