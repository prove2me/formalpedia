-- Prove2me | solution 1 for RH1E6S14.part_092_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T07:43:27.409895+00:00
-- url     : https://prove2.me/submissions/8c97fb3f-c781-4f6e-9312-66aa33168f05

import Definitions.Def_RH1E6S14_D092_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0738 : RS5.BandZeros ((55703598691 : ℝ) / 65536) ((55705600000 : ℝ) / 65536) 56 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0738.s0 RH1E6S14_0738.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0738.s0 RH1E6S14_0738.rest = RH1E6S14_0738.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0738.s0 :: RH1E6S14_0738.rest) = 56 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0738.s0.t = ((55703598691 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0738.s0]
  have e1 : RH1E6S14_0738.sL.t = ((55705600000 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0738.sL]
  rw [e0, e1] at h
  exact h

theorem part_092_1 : RS5.BandZeros ((55703598691 : ℝ) / 65536) ((55705600000 : ℝ) / 65536) 56 := by
  exact band_0738

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((55703598691 : ℝ) / 65536) ((55705600000 : ℝ) / 65536) 56 := by
  apply RH1E6S14.part_092_1 <;> assumption
