-- Prove2me | solution 1 for RH1E6S10.part_071_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T02:12:53.542257+00:00
-- url     : https://prove2.me/submissions/4533a195-fc99-49bc-824b-2461543f4855

import Definitions.Def_RH1E6S10_D071_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0574 : RS5.BandZeros ((41931996472 : ℝ) / 65536) ((41936540547 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0574.s0 RH1E6S10_0574.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0574.s0 RH1E6S10_0574.rest = RH1E6S10_0574.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0574.s0 :: RH1E6S10_0574.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0574.s0.t = ((41931996472 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0574.s0]
  have e1 : RH1E6S10_0574.sL.t = ((41936540547 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0574.sL]
  rw [e0, e1] at h
  exact h

theorem band_0575 : RS5.BandZeros ((41936540547 : ℝ) / 65536) ((41941084578 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0575.s0 RH1E6S10_0575.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0575.s0 RH1E6S10_0575.rest = RH1E6S10_0575.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0575.s0 :: RH1E6S10_0575.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0575.s0.t = ((41936540547 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0575.s0]
  have e1 : RH1E6S10_0575.sL.t = ((41941084578 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0575.sL]
  rw [e0, e1] at h
  exact h

theorem part_071_3 : RS5.BandZeros ((41931996472 : ℝ) / 65536) ((41941084578 : ℝ) / 65536) 254 := by
  have g0 := band_0574
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0575
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((41931996472 : ℝ) / 65536) ((41941084578 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_071_3 <;> assumption
