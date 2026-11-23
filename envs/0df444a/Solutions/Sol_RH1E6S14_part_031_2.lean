-- Prove2me | solution 1 for RH1E6S14.part_031_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T04:23:25.942819+00:00
-- url     : https://prove2.me/submissions/256ab669-730a-4feb-900f-47638b5c7656

import Definitions.Def_RH1E6S14_D031_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0252 : RS5.BandZeros ((53548936858 : ℝ) / 65536) ((53553377828 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0252.s0 RH1E6S14_0252.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0252.s0 RH1E6S14_0252.rest = RH1E6S14_0252.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0252.s0 :: RH1E6S14_0252.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0252.s0.t = ((53548936858 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0252.s0]
  have e1 : RH1E6S14_0252.sL.t = ((53553377828 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0252.sL]
  rw [e0, e1] at h
  exact h

theorem band_0253 : RS5.BandZeros ((53553377828 : ℝ) / 65536) ((53557801283 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0253.s0 RH1E6S14_0253.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0253.s0 RH1E6S14_0253.rest = RH1E6S14_0253.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0253.s0 :: RH1E6S14_0253.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0253.s0.t = ((53553377828 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0253.s0]
  have e1 : RH1E6S14_0253.sL.t = ((53557801283 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0253.sL]
  rw [e0, e1] at h
  exact h

theorem part_031_2 : RS5.BandZeros ((53548936858 : ℝ) / 65536) ((53557801283 : ℝ) / 65536) 254 := by
  have g0 := band_0252
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0253
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((53548936858 : ℝ) / 65536) ((53557801283 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_031_2 <;> assumption
