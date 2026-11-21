-- Prove2me | solution 1 for RH1E6S04.part_021_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T09:13:07.731189+00:00
-- url     : https://prove2.me/submissions/862f970b-90cb-4537-8bff-50e30b76509a

import Definitions.Def_RH1E6S04_D021_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0174 : RS5.BandZeros ((20503741254 : ℝ) / 65536) ((20508576366 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0174.s0 RH1E6S04_0174.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0174.s0 RH1E6S04_0174.rest = RH1E6S04_0174.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0174.s0 :: RH1E6S04_0174.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0174.s0.t = ((20503741254 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0174.s0]
  have e1 : RH1E6S04_0174.sL.t = ((20508576366 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0174.sL]
  rw [e0, e1] at h
  exact h

theorem band_0175 : RS5.BandZeros ((20508576366 : ℝ) / 65536) ((20513420890 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0175.s0 RH1E6S04_0175.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0175.s0 RH1E6S04_0175.rest = RH1E6S04_0175.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0175.s0 :: RH1E6S04_0175.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0175.s0.t = ((20508576366 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0175.s0]
  have e1 : RH1E6S04_0175.sL.t = ((20513420890 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0175.sL]
  rw [e0, e1] at h
  exact h

theorem part_021_3 : RS5.BandZeros ((20503741254 : ℝ) / 65536) ((20513420890 : ℝ) / 65536) 254 := by
  have g0 := band_0174
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0175
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((20503741254 : ℝ) / 65536) ((20513420890 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_021_3 <;> assumption
