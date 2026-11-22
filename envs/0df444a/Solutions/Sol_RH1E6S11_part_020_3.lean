-- Prove2me | solution 1 for RH1E6S11.part_020_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T03:59:58.544815+00:00
-- url     : https://prove2.me/submissions/297b4e3c-75b9-4f5a-bd6e-a721027a4df4

import Definitions.Def_RH1E6S11_D020_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0166 : RS5.BandZeros ((43349636501 : ℝ) / 65536) ((43354158610 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0166.s0 RH1E6S11_0166.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0166.s0 RH1E6S11_0166.rest = RH1E6S11_0166.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0166.s0 :: RH1E6S11_0166.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0166.s0.t = ((43349636501 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0166.s0]
  have e1 : RH1E6S11_0166.sL.t = ((43354158610 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0166.sL]
  rw [e0, e1] at h
  exact h

theorem band_0167 : RS5.BandZeros ((43354158610 : ℝ) / 65536) ((43358680678 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0167.s0 RH1E6S11_0167.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0167.s0 RH1E6S11_0167.rest = RH1E6S11_0167.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0167.s0 :: RH1E6S11_0167.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0167.s0.t = ((43354158610 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0167.s0]
  have e1 : RH1E6S11_0167.sL.t = ((43358680678 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0167.sL]
  rw [e0, e1] at h
  exact h

theorem part_020_3 : RS5.BandZeros ((43349636501 : ℝ) / 65536) ((43358680678 : ℝ) / 65536) 254 := by
  have g0 := band_0166
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0167
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((43349636501 : ℝ) / 65536) ((43358680678 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_020_3 <;> assumption
