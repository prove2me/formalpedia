-- Prove2me | solution 1 for RH1E6S12.part_027_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T08:46:03.759191+00:00
-- url     : https://prove2.me/submissions/006cd22e-72fc-4faa-95e6-c93cf9aa84d5

import Definitions.Def_RH1E6S12_D027_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0222 : RS5.BandZeros ((46873312894 : ℝ) / 65536) ((46877809112 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0222.s0 RH1E6S12_0222.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0222.s0 RH1E6S12_0222.rest = RH1E6S12_0222.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0222.s0 :: RH1E6S12_0222.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0222.s0.t = ((46873312894 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0222.s0]
  have e1 : RH1E6S12_0222.sL.t = ((46877809112 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0222.sL]
  rw [e0, e1] at h
  exact h

theorem band_0223 : RS5.BandZeros ((46877809112 : ℝ) / 65536) ((46882292750 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0223.s0 RH1E6S12_0223.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0223.s0 RH1E6S12_0223.rest = RH1E6S12_0223.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0223.s0 :: RH1E6S12_0223.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0223.s0.t = ((46877809112 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0223.s0]
  have e1 : RH1E6S12_0223.sL.t = ((46882292750 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0223.sL]
  rw [e0, e1] at h
  exact h

theorem part_027_3 : RS5.BandZeros ((46873312894 : ℝ) / 65536) ((46882292750 : ℝ) / 65536) 254 := by
  have g0 := band_0222
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0223
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((46873312894 : ℝ) / 65536) ((46882292750 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_027_3 <;> assumption
