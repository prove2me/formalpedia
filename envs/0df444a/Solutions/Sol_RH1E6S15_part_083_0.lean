-- Prove2me | solution 1 for RH1E6S15.part_083_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T13:09:07.883838+00:00
-- url     : https://prove2.me/submissions/625492c9-197d-4a3b-821d-8e2474fceb9a

import Definitions.Def_RH1E6S15_D083_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0664 : RS5.BandZeros ((58638113307 : ℝ) / 65536) ((58642495019 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0664.s0 RH1E6S15_0664.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0664.s0 RH1E6S15_0664.rest = RH1E6S15_0664.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0664.s0 :: RH1E6S15_0664.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0664.s0.t = ((58638113307 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0664.s0]
  have e1 : RH1E6S15_0664.sL.t = ((58642495019 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0664.sL]
  rw [e0, e1] at h
  exact h

theorem band_0665 : RS5.BandZeros ((58642495019 : ℝ) / 65536) ((58646918592 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0665.s0 RH1E6S15_0665.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0665.s0 RH1E6S15_0665.rest = RH1E6S15_0665.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0665.s0 :: RH1E6S15_0665.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0665.s0.t = ((58642495019 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0665.s0]
  have e1 : RH1E6S15_0665.sL.t = ((58646918592 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0665.sL]
  rw [e0, e1] at h
  exact h

theorem part_083_0 : RS5.BandZeros ((58638113307 : ℝ) / 65536) ((58646918592 : ℝ) / 65536) 254 := by
  have g0 := band_0664
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0665
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((58638113307 : ℝ) / 65536) ((58646918592 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_083_0 <;> assumption
