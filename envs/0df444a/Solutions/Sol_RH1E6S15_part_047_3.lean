-- Prove2me | solution 1 for RH1E6S15.part_047_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T10:44:08.91617+00:00
-- url     : https://prove2.me/submissions/766db164-87d1-4a5a-a63a-d69b9c76626a

import Definitions.Def_RH1E6S15_D047_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0382 : RS5.BandZeros ((57394208553 : ℝ) / 65536) ((57398618817 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0382.s0 RH1E6S15_0382.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0382.s0 RH1E6S15_0382.rest = RH1E6S15_0382.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0382.s0 :: RH1E6S15_0382.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0382.s0.t = ((57394208553 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0382.s0]
  have e1 : RH1E6S15_0382.sL.t = ((57398618817 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0382.sL]
  rw [e0, e1] at h
  exact h

theorem band_0383 : RS5.BandZeros ((57398618817 : ℝ) / 65536) ((57403038467 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0383.s0 RH1E6S15_0383.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0383.s0 RH1E6S15_0383.rest = RH1E6S15_0383.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0383.s0 :: RH1E6S15_0383.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0383.s0.t = ((57398618817 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0383.s0]
  have e1 : RH1E6S15_0383.sL.t = ((57403038467 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0383.sL]
  rw [e0, e1] at h
  exact h

theorem part_047_3 : RS5.BandZeros ((57394208553 : ℝ) / 65536) ((57403038467 : ℝ) / 65536) 254 := by
  have g0 := band_0382
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0383
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((57394208553 : ℝ) / 65536) ((57403038467 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_047_3 <;> assumption
