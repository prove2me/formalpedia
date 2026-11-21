-- Prove2me | solution 1 for RH1E6S04.part_047_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T10:12:48.87829+00:00
-- url     : https://prove2.me/submissions/82c60d4b-9b5b-4d1a-abc0-df6a951ee2e4

import Definitions.Def_RH1E6S04_D047_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0382 : RS5.BandZeros ((21507230689 : ℝ) / 65536) ((21512044536 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0382.s0 RH1E6S04_0382.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0382.s0 RH1E6S04_0382.rest = RH1E6S04_0382.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0382.s0 :: RH1E6S04_0382.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0382.s0.t = ((21507230689 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0382.s0]
  have e1 : RH1E6S04_0382.sL.t = ((21512044536 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0382.sL]
  rw [e0, e1] at h
  exact h

theorem band_0383 : RS5.BandZeros ((21512044536 : ℝ) / 65536) ((21516848809 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0383.s0 RH1E6S04_0383.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0383.s0 RH1E6S04_0383.rest = RH1E6S04_0383.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0383.s0 :: RH1E6S04_0383.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0383.s0.t = ((21512044536 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0383.s0]
  have e1 : RH1E6S04_0383.sL.t = ((21516848809 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0383.sL]
  rw [e0, e1] at h
  exact h

theorem part_047_3 : RS5.BandZeros ((21507230689 : ℝ) / 65536) ((21516848809 : ℝ) / 65536) 254 := by
  have g0 := band_0382
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0383
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((21507230689 : ℝ) / 65536) ((21516848809 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_047_3 <;> assumption
