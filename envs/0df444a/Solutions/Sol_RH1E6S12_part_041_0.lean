-- Prove2me | solution 1 for RH1E6S12.part_041_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T09:23:46.184517+00:00
-- url     : https://prove2.me/submissions/02420d49-3d83-44d8-a685-15d60ad76b09

import Definitions.Def_RH1E6S12_D041_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0328 : RS5.BandZeros ((47349220917 : ℝ) / 65536) ((47353719588 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0328.s0 RH1E6S12_0328.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0328.s0 RH1E6S12_0328.rest = RH1E6S12_0328.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0328.s0 :: RH1E6S12_0328.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0328.s0.t = ((47349220917 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0328.s0]
  have e1 : RH1E6S12_0328.sL.t = ((47353719588 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0328.sL]
  rw [e0, e1] at h
  exact h

theorem band_0329 : RS5.BandZeros ((47353719588 : ℝ) / 65536) ((47358198579 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0329.s0 RH1E6S12_0329.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0329.s0 RH1E6S12_0329.rest = RH1E6S12_0329.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0329.s0 :: RH1E6S12_0329.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0329.s0.t = ((47353719588 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0329.s0]
  have e1 : RH1E6S12_0329.sL.t = ((47358198579 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0329.sL]
  rw [e0, e1] at h
  exact h

theorem part_041_0 : RS5.BandZeros ((47349220917 : ℝ) / 65536) ((47358198579 : ℝ) / 65536) 254 := by
  have g0 := band_0328
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0329
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((47349220917 : ℝ) / 65536) ((47358198579 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_041_0 <;> assumption
