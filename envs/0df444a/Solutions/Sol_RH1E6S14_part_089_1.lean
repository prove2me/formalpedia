-- Prove2me | solution 1 for RH1E6S14.part_089_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T07:34:27.116084+00:00
-- url     : https://prove2.me/submissions/807fd3f7-47f5-4984-bdea-0fb0c4ddade0

import Definitions.Def_RH1E6S14_D089_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0714 : RS5.BandZeros ((55597375840 : ℝ) / 65536) ((55601807565 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0714.s0 RH1E6S14_0714.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0714.s0 RH1E6S14_0714.rest = RH1E6S14_0714.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0714.s0 :: RH1E6S14_0714.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0714.s0.t = ((55597375840 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0714.s0]
  have e1 : RH1E6S14_0714.sL.t = ((55601807565 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0714.sL]
  rw [e0, e1] at h
  exact h

theorem band_0715 : RS5.BandZeros ((55601807565 : ℝ) / 65536) ((55606226482 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0715.s0 RH1E6S14_0715.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0715.s0 RH1E6S14_0715.rest = RH1E6S14_0715.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0715.s0 :: RH1E6S14_0715.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0715.s0.t = ((55601807565 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0715.s0]
  have e1 : RH1E6S14_0715.sL.t = ((55606226482 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0715.sL]
  rw [e0, e1] at h
  exact h

theorem part_089_1 : RS5.BandZeros ((55597375840 : ℝ) / 65536) ((55606226482 : ℝ) / 65536) 254 := by
  have g0 := band_0714
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0715
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((55597375840 : ℝ) / 65536) ((55606226482 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_089_1 <;> assumption
