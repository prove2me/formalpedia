-- Prove2me | solution 1 for RH1E6S01.part_071_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T01:49:03.865436+00:00
-- url     : https://prove2.me/submissions/3e1a8f35-db7f-4e0a-9888-ce531b8824eb

import Definitions.Def_RH1E6S01_D071_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0574 : RS5.BandZeros ((12768418438 : ℝ) / 65536) ((12773455034 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0574.s0 RH1E6S01_0574.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0574.s0 RH1E6S01_0574.rest = RH1E6S01_0574.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0574.s0 :: RH1E6S01_0574.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0574.s0.t = ((12768418438 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0574.s0]
  have e1 : RH1E6S01_0574.sL.t = ((12773455034 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0574.sL]
  rw [e0, e1] at h
  exact h

theorem band_0575 : RS5.BandZeros ((12773455034 : ℝ) / 65536) ((12778531251 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0575.s0 RH1E6S01_0575.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0575.s0 RH1E6S01_0575.rest = RH1E6S01_0575.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0575.s0 :: RH1E6S01_0575.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0575.s0.t = ((12773455034 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0575.s0]
  have e1 : RH1E6S01_0575.sL.t = ((12778531251 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0575.sL]
  rw [e0, e1] at h
  exact h

theorem part_071_3 : RS5.BandZeros ((12768418438 : ℝ) / 65536) ((12778531251 : ℝ) / 65536) 254 := by
  have g0 := band_0574
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0575
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((12768418438 : ℝ) / 65536) ((12778531251 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_071_3 <;> assumption
