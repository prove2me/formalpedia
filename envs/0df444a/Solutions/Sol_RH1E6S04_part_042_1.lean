-- Prove2me | solution 1 for RH1E6S04.part_042_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T09:58:01.247777+00:00
-- url     : https://prove2.me/submissions/475d65b9-edbf-488b-96e6-ec0591a545d4

import Definitions.Def_RH1E6S04_D042_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0338 : RS5.BandZeros ((21295313305 : ℝ) / 65536) ((21300131544 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0338.s0 RH1E6S04_0338.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0338.s0 RH1E6S04_0338.rest = RH1E6S04_0338.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0338.s0 :: RH1E6S04_0338.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0338.s0.t = ((21295313305 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0338.s0]
  have e1 : RH1E6S04_0338.sL.t = ((21300131544 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0338.sL]
  rw [e0, e1] at h
  exact h

theorem band_0339 : RS5.BandZeros ((21300131544 : ℝ) / 65536) ((21304959167 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0339.s0 RH1E6S04_0339.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0339.s0 RH1E6S04_0339.rest = RH1E6S04_0339.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0339.s0 :: RH1E6S04_0339.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0339.s0.t = ((21300131544 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0339.s0]
  have e1 : RH1E6S04_0339.sL.t = ((21304959167 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0339.sL]
  rw [e0, e1] at h
  exact h

theorem part_042_1 : RS5.BandZeros ((21295313305 : ℝ) / 65536) ((21304959167 : ℝ) / 65536) 254 := by
  have g0 := band_0338
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0339
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((21295313305 : ℝ) / 65536) ((21304959167 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_042_1 <;> assumption
