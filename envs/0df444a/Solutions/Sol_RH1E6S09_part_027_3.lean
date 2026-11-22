-- Prove2me | solution 1 for RH1E6S09.part_027_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T09:26:33.786739+00:00
-- url     : https://prove2.me/submissions/2546b41c-ff5e-4322-b428-4cd764fa9b7e

import Definitions.Def_RH1E6S09_D027_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0222 : RS5.BandZeros ((37063698415 : ℝ) / 65536) ((37068286719 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0222.s0 RH1E6S09_0222.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0222.s0 RH1E6S09_0222.rest = RH1E6S09_0222.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0222.s0 :: RH1E6S09_0222.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0222.s0.t = ((37063698415 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0222.s0]
  have e1 : RH1E6S09_0222.sL.t = ((37068286719 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0222.sL]
  rw [e0, e1] at h
  exact h

theorem band_0223 : RS5.BandZeros ((37068286719 : ℝ) / 65536) ((37072892996 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0223.s0 RH1E6S09_0223.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0223.s0 RH1E6S09_0223.rest = RH1E6S09_0223.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0223.s0 :: RH1E6S09_0223.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0223.s0.t = ((37068286719 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0223.s0]
  have e1 : RH1E6S09_0223.sL.t = ((37072892996 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0223.sL]
  rw [e0, e1] at h
  exact h

theorem part_027_3 : RS5.BandZeros ((37063698415 : ℝ) / 65536) ((37072892996 : ℝ) / 65536) 254 := by
  have g0 := band_0222
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0223
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((37063698415 : ℝ) / 65536) ((37072892996 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_027_3 <;> assumption
