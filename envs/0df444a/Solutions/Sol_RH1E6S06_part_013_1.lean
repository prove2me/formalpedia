-- Prove2me | solution 1 for RH1E6S06.part_013_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T17:46:06.019683+00:00
-- url     : https://prove2.me/submissions/f2995d56-c404-4019-a16a-83a186b5bdd3

import Definitions.Def_RH1E6S06_D013_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0106 : RS5.BandZeros ((26715109588 : ℝ) / 65536) ((26719838531 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0106.s0 RH1E6S06_0106.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0106.s0 RH1E6S06_0106.rest = RH1E6S06_0106.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0106.s0 :: RH1E6S06_0106.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0106.s0.t = ((26715109588 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0106.s0]
  have e1 : RH1E6S06_0106.sL.t = ((26719838531 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0106.sL]
  rw [e0, e1] at h
  exact h

theorem band_0107 : RS5.BandZeros ((26719838531 : ℝ) / 65536) ((26724543995 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0107.s0 RH1E6S06_0107.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0107.s0 RH1E6S06_0107.rest = RH1E6S06_0107.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0107.s0 :: RH1E6S06_0107.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0107.s0.t = ((26719838531 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0107.s0]
  have e1 : RH1E6S06_0107.sL.t = ((26724543995 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0107.sL]
  rw [e0, e1] at h
  exact h

theorem part_013_1 : RS5.BandZeros ((26715109588 : ℝ) / 65536) ((26724543995 : ℝ) / 65536) 254 := by
  have g0 := band_0106
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0107
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((26715109588 : ℝ) / 65536) ((26724543995 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_013_1 <;> assumption
