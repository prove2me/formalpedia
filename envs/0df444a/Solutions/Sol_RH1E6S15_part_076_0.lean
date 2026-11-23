-- Prove2me | solution 1 for RH1E6S15.part_076_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T12:36:37.604195+00:00
-- url     : https://prove2.me/submissions/476df3ed-04ee-4a14-94f3-78e25ca68822

import Definitions.Def_RH1E6S15_D076_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0608 : RS5.BandZeros ((58391250975 : ℝ) / 65536) ((58395682576 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0608.s0 RH1E6S15_0608.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0608.s0 RH1E6S15_0608.rest = RH1E6S15_0608.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0608.s0 :: RH1E6S15_0608.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0608.s0.t = ((58391250975 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0608.s0]
  have e1 : RH1E6S15_0608.sL.t = ((58395682576 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0608.sL]
  rw [e0, e1] at h
  exact h

theorem band_0609 : RS5.BandZeros ((58395682576 : ℝ) / 65536) ((58400083797 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0609.s0 RH1E6S15_0609.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0609.s0 RH1E6S15_0609.rest = RH1E6S15_0609.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0609.s0 :: RH1E6S15_0609.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0609.s0.t = ((58395682576 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0609.s0]
  have e1 : RH1E6S15_0609.sL.t = ((58400083797 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0609.sL]
  rw [e0, e1] at h
  exact h

theorem part_076_0 : RS5.BandZeros ((58391250975 : ℝ) / 65536) ((58400083797 : ℝ) / 65536) 254 := by
  have g0 := band_0608
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0609
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((58391250975 : ℝ) / 65536) ((58400083797 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_076_0 <;> assumption
