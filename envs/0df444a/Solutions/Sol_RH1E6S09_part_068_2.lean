-- Prove2me | solution 1 for RH1E6S09.part_068_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T14:13:25.550673+00:00
-- url     : https://prove2.me/submissions/6a3b0f71-ae4b-43ad-88b5-a6f1694940fa

import Definitions.Def_RH1E6S09_D068_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0548 : RS5.BandZeros ((38555584397 : ℝ) / 65536) ((38560141356 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0548.s0 RH1E6S09_0548.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0548.s0 RH1E6S09_0548.rest = RH1E6S09_0548.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0548.s0 :: RH1E6S09_0548.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0548.s0.t = ((38555584397 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0548.s0]
  have e1 : RH1E6S09_0548.sL.t = ((38560141356 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0548.sL]
  rw [e0, e1] at h
  exact h

theorem band_0549 : RS5.BandZeros ((38560141356 : ℝ) / 65536) ((38564707110 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0549.s0 RH1E6S09_0549.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0549.s0 RH1E6S09_0549.rest = RH1E6S09_0549.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0549.s0 :: RH1E6S09_0549.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0549.s0.t = ((38560141356 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0549.s0]
  have e1 : RH1E6S09_0549.sL.t = ((38564707110 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0549.sL]
  rw [e0, e1] at h
  exact h

theorem part_068_2 : RS5.BandZeros ((38555584397 : ℝ) / 65536) ((38564707110 : ℝ) / 65536) 254 := by
  have g0 := band_0548
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0549
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((38555584397 : ℝ) / 65536) ((38564707110 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_068_2 <;> assumption
