-- Prove2me | solution 1 for RH1E6S02.part_039_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T03:29:59.767284+00:00
-- url     : https://prove2.me/submissions/74ba4f41-8f29-402d-a9b1-02f2bffc009c

import Definitions.Def_RH1E6S02_D039_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0312 : RS5.BandZeros ((14672209753 : ℝ) / 65536) ((14677199221 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0312.s0 RH1E6S02_0312.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0312.s0 RH1E6S02_0312.rest = RH1E6S02_0312.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0312.s0 :: RH1E6S02_0312.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0312.s0.t = ((14672209753 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0312.s0]
  have e1 : RH1E6S02_0312.sL.t = ((14677199221 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0312.sL]
  rw [e0, e1] at h
  exact h

theorem band_0313 : RS5.BandZeros ((14677199221 : ℝ) / 65536) ((14682178705 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0313.s0 RH1E6S02_0313.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0313.s0 RH1E6S02_0313.rest = RH1E6S02_0313.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0313.s0 :: RH1E6S02_0313.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0313.s0.t = ((14677199221 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0313.s0]
  have e1 : RH1E6S02_0313.sL.t = ((14682178705 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0313.sL]
  rw [e0, e1] at h
  exact h

theorem part_039_0 : RS5.BandZeros ((14672209753 : ℝ) / 65536) ((14682178705 : ℝ) / 65536) 254 := by
  have g0 := band_0312
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0313
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((14672209753 : ℝ) / 65536) ((14682178705 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_039_0 <;> assumption
