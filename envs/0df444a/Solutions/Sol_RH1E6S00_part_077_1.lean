-- Prove2me | solution 1 for RH1E6S00.part_077_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T23:22:54.255159+00:00
-- url     : https://prove2.me/submissions/cc542e6e-8435-4f4e-b2f9-07f30af9d758

import Definitions.Def_RH1E6S00_D077_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0618 : RS5.BandZeros ((9821130343 : ℝ) / 65536) ((9826298040 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0618.s0 RH1E6S00_0618.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0618.s0 RH1E6S00_0618.rest = RH1E6S00_0618.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0618.s0 :: RH1E6S00_0618.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0618.s0.t = ((9821130343 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0618.s0]
  have e1 : RH1E6S00_0618.sL.t = ((9826298040 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0618.sL]
  rw [e0, e1] at h
  exact h

theorem band_0619 : RS5.BandZeros ((9826298040 : ℝ) / 65536) ((9830400000 : ℝ) / 65536) 100 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0619.s0 RH1E6S00_0619.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0619.s0 RH1E6S00_0619.rest = RH1E6S00_0619.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0619.s0 :: RH1E6S00_0619.rest) = 100 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0619.s0.t = ((9826298040 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0619.s0]
  have e1 : RH1E6S00_0619.sL.t = ((9830400000 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0619.sL]
  rw [e0, e1] at h
  exact h

theorem part_077_1 : RS5.BandZeros ((9821130343 : ℝ) / 65536) ((9830400000 : ℝ) / 65536) 227 := by
  have g0 := band_0618
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0619
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((9821130343 : ℝ) / 65536) ((9830400000 : ℝ) / 65536) 227 := by
  apply RH1E6S00.part_077_1 <;> assumption
