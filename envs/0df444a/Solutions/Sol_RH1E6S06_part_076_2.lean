-- Prove2me | solution 1 for RH1E6S06.part_076_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T22:19:15.641775+00:00
-- url     : https://prove2.me/submissions/2b7b7ec4-d94c-401e-aee2-bcfc05bf1f04

import Definitions.Def_RH1E6S06_D076_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0612 : RS5.BandZeros ((29093986184 : ℝ) / 65536) ((29098687461 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0612.s0 RH1E6S06_0612.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0612.s0 RH1E6S06_0612.rest = RH1E6S06_0612.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0612.s0 :: RH1E6S06_0612.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0612.s0.t = ((29093986184 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0612.s0]
  have e1 : RH1E6S06_0612.sL.t = ((29098687461 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0612.sL]
  rw [e0, e1] at h
  exact h

theorem band_0613 : RS5.BandZeros ((29098687461 : ℝ) / 65536) ((29103363868 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0613.s0 RH1E6S06_0613.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0613.s0 RH1E6S06_0613.rest = RH1E6S06_0613.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0613.s0 :: RH1E6S06_0613.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0613.s0.t = ((29098687461 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0613.s0]
  have e1 : RH1E6S06_0613.sL.t = ((29103363868 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0613.sL]
  rw [e0, e1] at h
  exact h

theorem part_076_2 : RS5.BandZeros ((29093986184 : ℝ) / 65536) ((29103363868 : ℝ) / 65536) 254 := by
  have g0 := band_0612
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0613
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((29093986184 : ℝ) / 65536) ((29103363868 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_076_2 <;> assumption
