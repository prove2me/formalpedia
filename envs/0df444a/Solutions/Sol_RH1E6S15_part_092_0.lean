-- Prove2me | solution 1 for RH1E6S15.part_092_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T13:44:49.739504+00:00
-- url     : https://prove2.me/submissions/0c348785-4a02-428f-89b4-65660d7818c2

import Definitions.Def_RH1E6S15_D092_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0736 : RS5.BandZeros ((58955345706 : ℝ) / 65536) ((58959742026 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0736.s0 RH1E6S15_0736.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0736.s0 RH1E6S15_0736.rest = RH1E6S15_0736.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0736.s0 :: RH1E6S15_0736.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0736.s0.t = ((58955345706 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0736.s0]
  have e1 : RH1E6S15_0736.sL.t = ((58959742026 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0736.sL]
  rw [e0, e1] at h
  exact h

theorem band_0737 : RS5.BandZeros ((58959742026 : ℝ) / 65536) ((58964147828 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0737.s0 RH1E6S15_0737.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0737.s0 RH1E6S15_0737.rest = RH1E6S15_0737.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0737.s0 :: RH1E6S15_0737.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0737.s0.t = ((58959742026 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0737.s0]
  have e1 : RH1E6S15_0737.sL.t = ((58964147828 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0737.sL]
  rw [e0, e1] at h
  exact h

theorem part_092_0 : RS5.BandZeros ((58955345706 : ℝ) / 65536) ((58964147828 : ℝ) / 65536) 254 := by
  have g0 := band_0736
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0737
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((58955345706 : ℝ) / 65536) ((58964147828 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_092_0 <;> assumption
