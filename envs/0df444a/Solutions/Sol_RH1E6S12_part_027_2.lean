-- Prove2me | solution 1 for RH1E6S12.part_027_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T08:46:01.621539+00:00
-- url     : https://prove2.me/submissions/d234aa0a-15c0-4e8f-a759-78edc30b8edd

import Definitions.Def_RH1E6S12_D027_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0220 : RS5.BandZeros ((46864326845 : ℝ) / 65536) ((46868824648 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0220.s0 RH1E6S12_0220.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0220.s0 RH1E6S12_0220.rest = RH1E6S12_0220.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0220.s0 :: RH1E6S12_0220.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0220.s0.t = ((46864326845 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0220.s0]
  have e1 : RH1E6S12_0220.sL.t = ((46868824648 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0220.sL]
  rw [e0, e1] at h
  exact h

theorem band_0221 : RS5.BandZeros ((46868824648 : ℝ) / 65536) ((46873312894 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0221.s0 RH1E6S12_0221.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0221.s0 RH1E6S12_0221.rest = RH1E6S12_0221.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0221.s0 :: RH1E6S12_0221.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0221.s0.t = ((46868824648 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0221.s0]
  have e1 : RH1E6S12_0221.sL.t = ((46873312894 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0221.sL]
  rw [e0, e1] at h
  exact h

theorem part_027_2 : RS5.BandZeros ((46864326845 : ℝ) / 65536) ((46873312894 : ℝ) / 65536) 254 := by
  have g0 := band_0220
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0221
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((46864326845 : ℝ) / 65536) ((46873312894 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_027_2 <;> assumption
