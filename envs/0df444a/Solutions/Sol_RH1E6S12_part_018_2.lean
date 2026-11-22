-- Prove2me | solution 1 for RH1E6S12.part_018_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T08:20:03.693308+00:00
-- url     : https://prove2.me/submissions/96af5f0a-9165-45e8-8d57-53835fd77b32

import Definitions.Def_RH1E6S12_D018_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0148 : RS5.BandZeros ((46540808788 : ℝ) / 65536) ((46545320986 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0148.s0 RH1E6S12_0148.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0148.s0 RH1E6S12_0148.rest = RH1E6S12_0148.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0148.s0 :: RH1E6S12_0148.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0148.s0.t = ((46540808788 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0148.s0]
  have e1 : RH1E6S12_0148.sL.t = ((46545320986 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0148.sL]
  rw [e0, e1] at h
  exact h

theorem band_0149 : RS5.BandZeros ((46545320986 : ℝ) / 65536) ((46549808228 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0149.s0 RH1E6S12_0149.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0149.s0 RH1E6S12_0149.rest = RH1E6S12_0149.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0149.s0 :: RH1E6S12_0149.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0149.s0.t = ((46545320986 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0149.s0]
  have e1 : RH1E6S12_0149.sL.t = ((46549808228 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0149.sL]
  rw [e0, e1] at h
  exact h

theorem part_018_2 : RS5.BandZeros ((46540808788 : ℝ) / 65536) ((46549808228 : ℝ) / 65536) 254 := by
  have g0 := band_0148
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0149
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((46540808788 : ℝ) / 65536) ((46549808228 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_018_2 <;> assumption
