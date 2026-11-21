-- Prove2me | solution 1 for RH1E6S03.part_032_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T06:25:31.254598+00:00
-- url     : https://prove2.me/submissions/1171dfd7-f5d6-46fd-a7da-b57fff8a4851

import Definitions.Def_RH1E6S03_D032_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0256 : RS5.BandZeros ((17643542897 : ℝ) / 65536) ((17648436456 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0256.s0 RH1E6S03_0256.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0256.s0 RH1E6S03_0256.rest = RH1E6S03_0256.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0256.s0 :: RH1E6S03_0256.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0256.s0.t = ((17643542897 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0256.s0]
  have e1 : RH1E6S03_0256.sL.t = ((17648436456 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0256.sL]
  rw [e0, e1] at h
  exact h

theorem band_0257 : RS5.BandZeros ((17648436456 : ℝ) / 65536) ((17653368494 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0257.s0 RH1E6S03_0257.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0257.s0 RH1E6S03_0257.rest = RH1E6S03_0257.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0257.s0 :: RH1E6S03_0257.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0257.s0.t = ((17648436456 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0257.s0]
  have e1 : RH1E6S03_0257.sL.t = ((17653368494 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0257.sL]
  rw [e0, e1] at h
  exact h

theorem part_032_0 : RS5.BandZeros ((17643542897 : ℝ) / 65536) ((17653368494 : ℝ) / 65536) 254 := by
  have g0 := band_0256
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0257
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((17643542897 : ℝ) / 65536) ((17653368494 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_032_0 <;> assumption
