-- Prove2me | solution 1 for RH1E6S05.part_070_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T16:05:27.434824+00:00
-- url     : https://prove2.me/submissions/31903a52-39f9-4d8f-9194-3f49b8a5b416

import Definitions.Def_RH1E6S05_D070_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0564 : RS5.BandZeros ((25622789953 : ℝ) / 65536) ((25627555429 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0564.s0 RH1E6S05_0564.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0564.s0 RH1E6S05_0564.rest = RH1E6S05_0564.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0564.s0 :: RH1E6S05_0564.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0564.s0.t = ((25622789953 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0564.s0]
  have e1 : RH1E6S05_0564.sL.t = ((25627555429 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0564.sL]
  rw [e0, e1] at h
  exact h

theorem band_0565 : RS5.BandZeros ((25627555429 : ℝ) / 65536) ((25632264873 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0565.s0 RH1E6S05_0565.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0565.s0 RH1E6S05_0565.rest = RH1E6S05_0565.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0565.s0 :: RH1E6S05_0565.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0565.s0.t = ((25627555429 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0565.s0]
  have e1 : RH1E6S05_0565.sL.t = ((25632264873 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0565.sL]
  rw [e0, e1] at h
  exact h

theorem part_070_2 : RS5.BandZeros ((25622789953 : ℝ) / 65536) ((25632264873 : ℝ) / 65536) 254 := by
  have g0 := band_0564
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0565
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((25622789953 : ℝ) / 65536) ((25632264873 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_070_2 <;> assumption
