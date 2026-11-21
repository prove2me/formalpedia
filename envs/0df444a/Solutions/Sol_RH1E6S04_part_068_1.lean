-- Prove2me | solution 1 for RH1E6S04.part_068_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T10:58:03.239177+00:00
-- url     : https://prove2.me/submissions/a721e232-0d2b-4b64-9e3a-6d360e87a411

import Definitions.Def_RH1E6S04_D068_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0546 : RS5.BandZeros ((22295405855 : ℝ) / 65536) ((22300203809 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0546.s0 RH1E6S04_0546.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0546.s0 RH1E6S04_0546.rest = RH1E6S04_0546.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0546.s0 :: RH1E6S04_0546.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0546.s0.t = ((22295405855 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0546.s0]
  have e1 : RH1E6S04_0546.sL.t = ((22300203809 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0546.sL]
  rw [e0, e1] at h
  exact h

theorem band_0547 : RS5.BandZeros ((22300203809 : ℝ) / 65536) ((22304992223 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0547.s0 RH1E6S04_0547.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0547.s0 RH1E6S04_0547.rest = RH1E6S04_0547.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0547.s0 :: RH1E6S04_0547.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0547.s0.t = ((22300203809 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0547.s0]
  have e1 : RH1E6S04_0547.sL.t = ((22304992223 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0547.sL]
  rw [e0, e1] at h
  exact h

theorem part_068_1 : RS5.BandZeros ((22295405855 : ℝ) / 65536) ((22304992223 : ℝ) / 65536) 254 := by
  have g0 := band_0546
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0547
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((22295405855 : ℝ) / 65536) ((22304992223 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_068_1 <;> assumption
