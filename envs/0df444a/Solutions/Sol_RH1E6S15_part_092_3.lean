-- Prove2me | solution 1 for RH1E6S15.part_092_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T13:50:42.159599+00:00
-- url     : https://prove2.me/submissions/bf6b4b3e-7513-4210-8a39-ea1bdfb89bed

import Definitions.Def_RH1E6S15_D092_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0742 : RS5.BandZeros ((58981761998 : ℝ) / 65536) ((58982400000 : ℝ) / 65536) 18 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0742.s0 RH1E6S15_0742.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0742.s0 RH1E6S15_0742.rest = RH1E6S15_0742.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0742.s0 :: RH1E6S15_0742.rest) = 18 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0742.s0.t = ((58981761998 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0742.s0]
  have e1 : RH1E6S15_0742.sL.t = ((58982400000 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0742.sL]
  rw [e0, e1] at h
  exact h

theorem part_092_3 : RS5.BandZeros ((58981761998 : ℝ) / 65536) ((58982400000 : ℝ) / 65536) 18 := by
  exact band_0742

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((58981761998 : ℝ) / 65536) ((58982400000 : ℝ) / 65536) 18 := by
  apply RH1E6S15.part_092_3 <;> assumption
