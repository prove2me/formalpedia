-- Prove2me | solution 1 for RH1E6S10.part_001_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T16:58:14.118872+00:00
-- url     : https://prove2.me/submissions/20097f2c-92ee-40eb-8592-300ebed4f5f3

import Definitions.Def_RH1E6S10_D001_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0010 : RS5.BandZeros ((39367225086 : ℝ) / 65536) ((39371794168 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0010.s0 RH1E6S10_0010.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0010.s0 RH1E6S10_0010.rest = RH1E6S10_0010.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0010.s0 :: RH1E6S10_0010.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0010.s0.t = ((39367225086 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0010.s0]
  have e1 : RH1E6S10_0010.sL.t = ((39371794168 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0010.sL]
  rw [e0, e1] at h
  exact h

theorem band_0011 : RS5.BandZeros ((39371794168 : ℝ) / 65536) ((39376327298 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0011.s0 RH1E6S10_0011.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0011.s0 RH1E6S10_0011.rest = RH1E6S10_0011.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0011.s0 :: RH1E6S10_0011.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0011.s0.t = ((39371794168 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0011.s0]
  have e1 : RH1E6S10_0011.sL.t = ((39376327298 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0011.sL]
  rw [e0, e1] at h
  exact h

theorem part_001_1 : RS5.BandZeros ((39367225086 : ℝ) / 65536) ((39376327298 : ℝ) / 65536) 254 := by
  have g0 := band_0010
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0011
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((39367225086 : ℝ) / 65536) ((39376327298 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_001_1 <;> assumption
