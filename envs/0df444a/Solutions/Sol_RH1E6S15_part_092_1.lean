-- Prove2me | solution 1 for RH1E6S15.part_092_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T13:44:51.700928+00:00
-- url     : https://prove2.me/submissions/bc054db6-0141-4b7d-a0ee-998904a261d2

import Definitions.Def_RH1E6S15_D092_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0738 : RS5.BandZeros ((58964147828 : ℝ) / 65536) ((58968534584 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0738.s0 RH1E6S15_0738.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0738.s0 RH1E6S15_0738.rest = RH1E6S15_0738.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0738.s0 :: RH1E6S15_0738.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0738.s0.t = ((58964147828 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0738.s0]
  have e1 : RH1E6S15_0738.sL.t = ((58968534584 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0738.sL]
  rw [e0, e1] at h
  exact h

theorem band_0739 : RS5.BandZeros ((58968534584 : ℝ) / 65536) ((58972974176 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0739.s0 RH1E6S15_0739.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0739.s0 RH1E6S15_0739.rest = RH1E6S15_0739.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0739.s0 :: RH1E6S15_0739.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0739.s0.t = ((58968534584 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0739.s0]
  have e1 : RH1E6S15_0739.sL.t = ((58972974176 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0739.sL]
  rw [e0, e1] at h
  exact h

theorem part_092_1 : RS5.BandZeros ((58964147828 : ℝ) / 65536) ((58972974176 : ℝ) / 65536) 254 := by
  have g0 := band_0738
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0739
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((58964147828 : ℝ) / 65536) ((58972974176 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_092_1 <;> assumption
