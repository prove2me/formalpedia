-- Prove2me | solution 1 for RH1E6S11.part_047_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T05:16:20.898019+00:00
-- url     : https://prove2.me/submissions/a6c603a8-56d7-4e28-8c2b-9ee12eb365ac

import Definitions.Def_RH1E6S11_D047_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0382 : RS5.BandZeros ((44325464789 : ℝ) / 65536) ((44329995979 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0382.s0 RH1E6S11_0382.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0382.s0 RH1E6S11_0382.rest = RH1E6S11_0382.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0382.s0 :: RH1E6S11_0382.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0382.s0.t = ((44325464789 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0382.s0]
  have e1 : RH1E6S11_0382.sL.t = ((44329995979 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0382.sL]
  rw [e0, e1] at h
  exact h

theorem band_0383 : RS5.BandZeros ((44329995979 : ℝ) / 65536) ((44334509361 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0383.s0 RH1E6S11_0383.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0383.s0 RH1E6S11_0383.rest = RH1E6S11_0383.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0383.s0 :: RH1E6S11_0383.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0383.s0.t = ((44329995979 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0383.s0]
  have e1 : RH1E6S11_0383.sL.t = ((44334509361 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0383.sL]
  rw [e0, e1] at h
  exact h

theorem part_047_3 : RS5.BandZeros ((44325464789 : ℝ) / 65536) ((44334509361 : ℝ) / 65536) 254 := by
  have g0 := band_0382
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0383
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((44325464789 : ℝ) / 65536) ((44334509361 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_047_3 <;> assumption
