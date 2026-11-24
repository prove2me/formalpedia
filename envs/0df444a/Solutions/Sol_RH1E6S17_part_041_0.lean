-- Prove2me | solution 1 for RH1E6S17.part_041_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T21:54:29.566076+00:00
-- url     : https://prove2.me/submissions/d3207199-a993-4c39-bdae-536199f64d55

import Definitions.Def_RH1E6S17_D041_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0328 : RS5.BandZeros ((63696060714 : ℝ) / 65536) ((63700437195 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0328.s0 RH1E6S17_0328.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0328.s0 RH1E6S17_0328.rest = RH1E6S17_0328.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0328.s0 :: RH1E6S17_0328.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0328.s0.t = ((63696060714 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0328.s0]
  have e1 : RH1E6S17_0328.sL.t = ((63700437195 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0328.sL]
  rw [e0, e1] at h
  exact h

theorem band_0329 : RS5.BandZeros ((63700437195 : ℝ) / 65536) ((63704813650 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0329.s0 RH1E6S17_0329.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0329.s0 RH1E6S17_0329.rest = RH1E6S17_0329.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0329.s0 :: RH1E6S17_0329.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0329.s0.t = ((63700437195 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0329.s0]
  have e1 : RH1E6S17_0329.sL.t = ((63704813650 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0329.sL]
  rw [e0, e1] at h
  exact h

theorem part_041_0 : RS5.BandZeros ((63696060714 : ℝ) / 65536) ((63704813650 : ℝ) / 65536) 254 := by
  have g0 := band_0328
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0329
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((63696060714 : ℝ) / 65536) ((63704813650 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_041_0 <;> assumption
