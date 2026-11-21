-- Prove2me | solution 1 for RH1E6S06.part_040_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T18:58:04.990736+00:00
-- url     : https://prove2.me/submissions/600f3ca9-9c62-4514-85a6-e88b6b8c49fe

import Definitions.Def_RH1E6S06_D040_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0326 : RS5.BandZeros ((27751661272 : ℝ) / 65536) ((27756349016 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0326.s0 RH1E6S06_0326.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0326.s0 RH1E6S06_0326.rest = RH1E6S06_0326.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0326.s0 :: RH1E6S06_0326.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0326.s0.t = ((27751661272 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0326.s0]
  have e1 : RH1E6S06_0326.sL.t = ((27756349016 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0326.sL]
  rw [e0, e1] at h
  exact h

theorem band_0327 : RS5.BandZeros ((27756349016 : ℝ) / 65536) ((27761065982 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0327.s0 RH1E6S06_0327.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0327.s0 RH1E6S06_0327.rest = RH1E6S06_0327.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0327.s0 :: RH1E6S06_0327.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0327.s0.t = ((27756349016 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0327.s0]
  have e1 : RH1E6S06_0327.sL.t = ((27761065982 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0327.sL]
  rw [e0, e1] at h
  exact h

theorem part_040_3 : RS5.BandZeros ((27751661272 : ℝ) / 65536) ((27761065982 : ℝ) / 65536) 254 := by
  have g0 := band_0326
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0327
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((27751661272 : ℝ) / 65536) ((27761065982 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_040_3 <;> assumption
