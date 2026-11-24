-- Prove2me | solution 1 for RH1E6S17.part_082_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T00:11:50.062655+00:00
-- url     : https://prove2.me/submissions/8a9e2fd9-2e73-47d4-8560-449cde84c462

import Definitions.Def_RH1E6S17_D082_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0662 : RS5.BandZeros ((65156410457 : ℝ) / 65536) ((65160795849 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0662.s0 RH1E6S17_0662.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0662.s0 RH1E6S17_0662.rest = RH1E6S17_0662.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0662.s0 :: RH1E6S17_0662.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0662.s0.t = ((65156410457 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0662.s0]
  have e1 : RH1E6S17_0662.sL.t = ((65160795849 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0662.sL]
  rw [e0, e1] at h
  exact h

theorem band_0663 : RS5.BandZeros ((65160795849 : ℝ) / 65536) ((65165164019 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0663.s0 RH1E6S17_0663.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0663.s0 RH1E6S17_0663.rest = RH1E6S17_0663.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0663.s0 :: RH1E6S17_0663.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0663.s0.t = ((65160795849 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0663.s0]
  have e1 : RH1E6S17_0663.sL.t = ((65165164019 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0663.sL]
  rw [e0, e1] at h
  exact h

theorem part_082_3 : RS5.BandZeros ((65156410457 : ℝ) / 65536) ((65165164019 : ℝ) / 65536) 254 := by
  have g0 := band_0662
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0663
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((65156410457 : ℝ) / 65536) ((65165164019 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_082_3 <;> assumption
