-- Prove2me | solution 1 for RH1E6S11.part_003_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T03:12:14.507931+00:00
-- url     : https://prove2.me/submissions/8a0994c1-ef0c-4c3a-b7d8-4c4c9b925dd1

import Definitions.Def_RH1E6S11_D003_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0028 : RS5.BandZeros ((42725191885 : ℝ) / 65536) ((42729719675 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0028.s0 RH1E6S11_0028.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0028.s0 RH1E6S11_0028.rest = RH1E6S11_0028.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0028.s0 :: RH1E6S11_0028.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0028.s0.t = ((42725191885 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0028.s0]
  have e1 : RH1E6S11_0028.sL.t = ((42729719675 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0028.sL]
  rw [e0, e1] at h
  exact h

theorem band_0029 : RS5.BandZeros ((42729719675 : ℝ) / 65536) ((42734247423 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0029.s0 RH1E6S11_0029.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0029.s0 RH1E6S11_0029.rest = RH1E6S11_0029.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0029.s0 :: RH1E6S11_0029.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0029.s0.t = ((42729719675 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0029.s0]
  have e1 : RH1E6S11_0029.sL.t = ((42734247423 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0029.sL]
  rw [e0, e1] at h
  exact h

theorem part_003_2 : RS5.BandZeros ((42725191885 : ℝ) / 65536) ((42734247423 : ℝ) / 65536) 254 := by
  have g0 := band_0028
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0029
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((42725191885 : ℝ) / 65536) ((42734247423 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_003_2 <;> assumption
