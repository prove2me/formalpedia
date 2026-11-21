-- Prove2me | solution 1 for RH1E6S06.part_030_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T18:27:20.045665+00:00
-- url     : https://prove2.me/submissions/273254c3-ea06-4dee-8d9a-02a53adb5fe2

import Definitions.Def_RH1E6S06_D030_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0240 : RS5.BandZeros ((27346897502 : ℝ) / 65536) ((27351596393 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0240.s0 RH1E6S06_0240.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0240.s0 RH1E6S06_0240.rest = RH1E6S06_0240.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0240.s0 :: RH1E6S06_0240.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0240.s0.t = ((27346897502 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0240.s0]
  have e1 : RH1E6S06_0240.sL.t = ((27351596393 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0240.sL]
  rw [e0, e1] at h
  exact h

theorem band_0241 : RS5.BandZeros ((27351596393 : ℝ) / 65536) ((27356311577 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0241.s0 RH1E6S06_0241.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0241.s0 RH1E6S06_0241.rest = RH1E6S06_0241.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0241.s0 :: RH1E6S06_0241.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0241.s0.t = ((27351596393 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0241.s0]
  have e1 : RH1E6S06_0241.sL.t = ((27356311577 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0241.sL]
  rw [e0, e1] at h
  exact h

theorem part_030_0 : RS5.BandZeros ((27346897502 : ℝ) / 65536) ((27356311577 : ℝ) / 65536) 254 := by
  have g0 := band_0240
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0241
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((27346897502 : ℝ) / 65536) ((27356311577 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_030_0 <;> assumption
