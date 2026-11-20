-- Prove2me | solution 1 for RH1E6S01.part_016_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T23:53:56.962345+00:00
-- url     : https://prove2.me/submissions/704fafd8-803d-4c6f-89f2-9db76f21b15b

import Definitions.Def_RH1E6S01_D016_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0130 : RS5.BandZeros ((10502563928 : ℝ) / 65536) ((10507707614 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0130.s0 RH1E6S01_0130.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0130.s0 RH1E6S01_0130.rest = RH1E6S01_0130.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0130.s0 :: RH1E6S01_0130.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0130.s0.t = ((10502563928 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0130.s0]
  have e1 : RH1E6S01_0130.sL.t = ((10507707614 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0130.sL]
  rw [e0, e1] at h
  exact h

theorem band_0131 : RS5.BandZeros ((10507707614 : ℝ) / 65536) ((10512891630 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0131.s0 RH1E6S01_0131.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0131.s0 RH1E6S01_0131.rest = RH1E6S01_0131.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0131.s0 :: RH1E6S01_0131.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0131.s0.t = ((10507707614 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0131.s0]
  have e1 : RH1E6S01_0131.sL.t = ((10512891630 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0131.sL]
  rw [e0, e1] at h
  exact h

theorem part_016_1 : RS5.BandZeros ((10502563928 : ℝ) / 65536) ((10512891630 : ℝ) / 65536) 254 := by
  have g0 := band_0130
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0131
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((10502563928 : ℝ) / 65536) ((10512891630 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_016_1 <;> assumption
