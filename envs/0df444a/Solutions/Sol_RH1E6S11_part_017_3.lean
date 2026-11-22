-- Prove2me | solution 1 for RH1E6S11.part_017_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T03:51:37.851397+00:00
-- url     : https://prove2.me/submissions/2ea69110-083f-48c8-8114-8ed7a2f836f4

import Definitions.Def_RH1E6S11_D017_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0142 : RS5.BandZeros ((43241093641 : ℝ) / 65536) ((43245625634 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0142.s0 RH1E6S11_0142.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0142.s0 RH1E6S11_0142.rest = RH1E6S11_0142.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0142.s0 :: RH1E6S11_0142.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0142.s0.t = ((43241093641 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0142.s0]
  have e1 : RH1E6S11_0142.sL.t = ((43245625634 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0142.sL]
  rw [e0, e1] at h
  exact h

theorem band_0143 : RS5.BandZeros ((43245625634 : ℝ) / 65536) ((43250130875 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0143.s0 RH1E6S11_0143.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0143.s0 RH1E6S11_0143.rest = RH1E6S11_0143.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0143.s0 :: RH1E6S11_0143.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0143.s0.t = ((43245625634 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0143.s0]
  have e1 : RH1E6S11_0143.sL.t = ((43250130875 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0143.sL]
  rw [e0, e1] at h
  exact h

theorem part_017_3 : RS5.BandZeros ((43241093641 : ℝ) / 65536) ((43250130875 : ℝ) / 65536) 254 := by
  have g0 := band_0142
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0143
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((43241093641 : ℝ) / 65536) ((43250130875 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_017_3 <;> assumption
