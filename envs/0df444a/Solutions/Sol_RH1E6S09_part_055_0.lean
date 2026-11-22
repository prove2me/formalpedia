-- Prove2me | solution 1 for RH1E6S09.part_055_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T10:42:25.143095+00:00
-- url     : https://prove2.me/submissions/aa245308-107d-4648-b416-6b8200b64493

import Definitions.Def_RH1E6S09_D055_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0440 : RS5.BandZeros ((38061903720 : ℝ) / 65536) ((38066492635 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0440.s0 RH1E6S09_0440.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0440.s0 RH1E6S09_0440.rest = RH1E6S09_0440.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0440.s0 :: RH1E6S09_0440.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0440.s0.t = ((38061903720 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0440.s0]
  have e1 : RH1E6S09_0440.sL.t = ((38066492635 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0440.sL]
  rw [e0, e1] at h
  exact h

theorem band_0441 : RS5.BandZeros ((38066492635 : ℝ) / 65536) ((38071063658 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0441.s0 RH1E6S09_0441.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0441.s0 RH1E6S09_0441.rest = RH1E6S09_0441.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0441.s0 :: RH1E6S09_0441.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0441.s0.t = ((38066492635 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0441.s0]
  have e1 : RH1E6S09_0441.sL.t = ((38071063658 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0441.sL]
  rw [e0, e1] at h
  exact h

theorem part_055_0 : RS5.BandZeros ((38061903720 : ℝ) / 65536) ((38071063658 : ℝ) / 65536) 254 := by
  have g0 := band_0440
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0441
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((38061903720 : ℝ) / 65536) ((38071063658 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_055_0 <;> assumption
