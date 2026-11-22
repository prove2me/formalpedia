-- Prove2me | solution 1 for RH1E6S10.part_073_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T02:15:51.824967+00:00
-- url     : https://prove2.me/submissions/52539255-8b5b-4ef4-99c4-af8ca8347d52

import Definitions.Def_RH1E6S10_D073_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0588 : RS5.BandZeros ((41995484664 : ℝ) / 65536) ((42000028142 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0588.s0 RH1E6S10_0588.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0588.s0 RH1E6S10_0588.rest = RH1E6S10_0588.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0588.s0 :: RH1E6S10_0588.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0588.s0.t = ((41995484664 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0588.s0]
  have e1 : RH1E6S10_0588.sL.t = ((42000028142 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0588.sL]
  rw [e0, e1] at h
  exact h

theorem band_0589 : RS5.BandZeros ((42000028142 : ℝ) / 65536) ((42004553726 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0589.s0 RH1E6S10_0589.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0589.s0 RH1E6S10_0589.rest = RH1E6S10_0589.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0589.s0 :: RH1E6S10_0589.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0589.s0.t = ((42000028142 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0589.s0]
  have e1 : RH1E6S10_0589.sL.t = ((42004553726 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0589.sL]
  rw [e0, e1] at h
  exact h

theorem part_073_2 : RS5.BandZeros ((41995484664 : ℝ) / 65536) ((42004553726 : ℝ) / 65536) 254 := by
  have g0 := band_0588
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0589
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((41995484664 : ℝ) / 65536) ((42004553726 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_073_2 <;> assumption
