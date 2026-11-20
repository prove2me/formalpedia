-- Prove2me | solution 1 for RH1E6S01.part_006_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T23:34:57.980681+00:00
-- url     : https://prove2.me/submissions/17658d6d-01e8-46f1-ac82-09f11c4d91f7

import Definitions.Def_RH1E6S01_D006_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0052 : RS5.BandZeros ((10099804636 : ℝ) / 65536) ((10104958031 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0052.s0 RH1E6S01_0052.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0052.s0 RH1E6S01_0052.rest = RH1E6S01_0052.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0052.s0 :: RH1E6S01_0052.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0052.s0.t = ((10099804636 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0052.s0]
  have e1 : RH1E6S01_0052.sL.t = ((10104958031 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0052.sL]
  rw [e0, e1] at h
  exact h

theorem band_0053 : RS5.BandZeros ((10104958031 : ℝ) / 65536) ((10110131534 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0053.s0 RH1E6S01_0053.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0053.s0 RH1E6S01_0053.rest = RH1E6S01_0053.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0053.s0 :: RH1E6S01_0053.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0053.s0.t = ((10104958031 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0053.s0]
  have e1 : RH1E6S01_0053.sL.t = ((10110131534 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0053.sL]
  rw [e0, e1] at h
  exact h

theorem part_006_2 : RS5.BandZeros ((10099804636 : ℝ) / 65536) ((10110131534 : ℝ) / 65536) 254 := by
  have g0 := band_0052
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0053
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((10099804636 : ℝ) / 65536) ((10110131534 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_006_2 <;> assumption
