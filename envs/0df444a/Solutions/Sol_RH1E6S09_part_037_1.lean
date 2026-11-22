-- Prove2me | solution 1 for RH1E6S09.part_037_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T09:53:43.062876+00:00
-- url     : https://prove2.me/submissions/1ca9e647-4854-488e-960e-bd382e5f7432

import Definitions.Def_RH1E6S09_D037_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0298 : RS5.BandZeros ((37411978295 : ℝ) / 65536) ((37416556760 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0298.s0 RH1E6S09_0298.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0298.s0 RH1E6S09_0298.rest = RH1E6S09_0298.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0298.s0 :: RH1E6S09_0298.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0298.s0.t = ((37411978295 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0298.s0]
  have e1 : RH1E6S09_0298.sL.t = ((37416556760 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0298.sL]
  rw [e0, e1] at h
  exact h

theorem band_0299 : RS5.BandZeros ((37416556760 : ℝ) / 65536) ((37421126271 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0299.s0 RH1E6S09_0299.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0299.s0 RH1E6S09_0299.rest = RH1E6S09_0299.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0299.s0 :: RH1E6S09_0299.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0299.s0.t = ((37416556760 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0299.s0]
  have e1 : RH1E6S09_0299.sL.t = ((37421126271 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0299.sL]
  rw [e0, e1] at h
  exact h

theorem part_037_1 : RS5.BandZeros ((37411978295 : ℝ) / 65536) ((37421126271 : ℝ) / 65536) 254 := by
  have g0 := band_0298
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0299
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((37411978295 : ℝ) / 65536) ((37421126271 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_037_1 <;> assumption
