-- Prove2me | solution 1 for RH1E6S12.part_038_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T09:15:09.412007+00:00
-- url     : https://prove2.me/submissions/feedf359-404d-43d5-9e05-f256a9d8d0f8

import Definitions.Def_RH1E6S12_D038_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0306 : RS5.BandZeros ((47250480683 : ℝ) / 65536) ((47254978185 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0306.s0 RH1E6S12_0306.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0306.s0 RH1E6S12_0306.rest = RH1E6S12_0306.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0306.s0 :: RH1E6S12_0306.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0306.s0.t = ((47250480683 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0306.s0]
  have e1 : RH1E6S12_0306.sL.t = ((47254978185 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0306.sL]
  rw [e0, e1] at h
  exact h

theorem band_0307 : RS5.BandZeros ((47254978185 : ℝ) / 65536) ((47259462729 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0307.s0 RH1E6S12_0307.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0307.s0 RH1E6S12_0307.rest = RH1E6S12_0307.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0307.s0 :: RH1E6S12_0307.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0307.s0.t = ((47254978185 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0307.s0]
  have e1 : RH1E6S12_0307.sL.t = ((47259462729 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0307.sL]
  rw [e0, e1] at h
  exact h

theorem part_038_1 : RS5.BandZeros ((47250480683 : ℝ) / 65536) ((47259462729 : ℝ) / 65536) 254 := by
  have g0 := band_0306
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0307
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((47250480683 : ℝ) / 65536) ((47259462729 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_038_1 <;> assumption
