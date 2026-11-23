-- Prove2me | solution 1 for RH1E6S15.part_090_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T13:38:56.789864+00:00
-- url     : https://prove2.me/submissions/db75750e-2e40-4ffd-a198-edb3ce00942d

import Definitions.Def_RH1E6S15_D090_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0724 : RS5.BandZeros ((58902476685 : ℝ) / 65536) ((58906878966 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0724.s0 RH1E6S15_0724.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0724.s0 RH1E6S15_0724.rest = RH1E6S15_0724.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0724.s0 :: RH1E6S15_0724.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0724.s0.t = ((58902476685 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0724.s0]
  have e1 : RH1E6S15_0724.sL.t = ((58906878966 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0724.sL]
  rw [e0, e1] at h
  exact h

theorem band_0725 : RS5.BandZeros ((58906878966 : ℝ) / 65536) ((58911289882 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0725.s0 RH1E6S15_0725.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0725.s0 RH1E6S15_0725.rest = RH1E6S15_0725.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0725.s0 :: RH1E6S15_0725.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0725.s0.t = ((58906878966 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0725.s0]
  have e1 : RH1E6S15_0725.sL.t = ((58911289882 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0725.sL]
  rw [e0, e1] at h
  exact h

theorem part_090_2 : RS5.BandZeros ((58902476685 : ℝ) / 65536) ((58911289882 : ℝ) / 65536) 254 := by
  have g0 := band_0724
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0725
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((58902476685 : ℝ) / 65536) ((58911289882 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_090_2 <;> assumption
