-- Prove2me | solution 1 for RH1E6S11.part_007_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T03:23:28.888804+00:00
-- url     : https://prove2.me/submissions/1939ab00-e6c0-4ed1-93d6-c53cda9f0163

import Definitions.Def_RH1E6S11_D007_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0058 : RS5.BandZeros ((42860989698 : ℝ) / 65536) ((42865534064 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0058.s0 RH1E6S11_0058.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0058.s0 RH1E6S11_0058.rest = RH1E6S11_0058.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0058.s0 :: RH1E6S11_0058.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0058.s0.t = ((42860989698 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0058.s0]
  have e1 : RH1E6S11_0058.sL.t = ((42865534064 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0058.sL]
  rw [e0, e1] at h
  exact h

theorem band_0059 : RS5.BandZeros ((42865534064 : ℝ) / 65536) ((42870051658 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0059.s0 RH1E6S11_0059.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0059.s0 RH1E6S11_0059.rest = RH1E6S11_0059.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0059.s0 :: RH1E6S11_0059.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0059.s0.t = ((42865534064 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0059.s0]
  have e1 : RH1E6S11_0059.sL.t = ((42870051658 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0059.sL]
  rw [e0, e1] at h
  exact h

theorem part_007_1 : RS5.BandZeros ((42860989698 : ℝ) / 65536) ((42870051658 : ℝ) / 65536) 254 := by
  have g0 := band_0058
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0059
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((42860989698 : ℝ) / 65536) ((42870051658 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_007_1 <;> assumption
