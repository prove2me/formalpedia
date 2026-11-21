-- Prove2me | solution 1 for RH1E6S07.part_016_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T23:40:18.63378+00:00
-- url     : https://prove2.me/submissions/b3a43a10-ee74-4aae-b7a5-28916233d8ae

import Definitions.Def_RH1E6S07_D016_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0128 : RS5.BandZeros ((30089442354 : ℝ) / 65536) ((30094096768 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0128.s0 RH1E6S07_0128.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0128.s0 RH1E6S07_0128.rest = RH1E6S07_0128.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0128.s0 :: RH1E6S07_0128.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0128.s0.t = ((30089442354 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0128.s0]
  have e1 : RH1E6S07_0128.sL.t = ((30094096768 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0128.sL]
  rw [e0, e1] at h
  exact h

theorem band_0129 : RS5.BandZeros ((30094096768 : ℝ) / 65536) ((30098775369 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0129.s0 RH1E6S07_0129.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0129.s0 RH1E6S07_0129.rest = RH1E6S07_0129.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0129.s0 :: RH1E6S07_0129.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0129.s0.t = ((30094096768 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0129.s0]
  have e1 : RH1E6S07_0129.sL.t = ((30098775369 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0129.sL]
  rw [e0, e1] at h
  exact h

theorem part_016_0 : RS5.BandZeros ((30089442354 : ℝ) / 65536) ((30098775369 : ℝ) / 65536) 254 := by
  have g0 := band_0128
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0129
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((30089442354 : ℝ) / 65536) ((30098775369 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_016_0 <;> assumption
