-- Prove2me | solution 1 for RH1E6S07.part_015_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T23:37:38.528886+00:00
-- url     : https://prove2.me/submissions/e07d541d-2fad-491a-b9b5-d267b0ce6b15

import Definitions.Def_RH1E6S07_D015_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0122 : RS5.BandZeros ((30061417348 : ℝ) / 65536) ((30066089671 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0122.s0 RH1E6S07_0122.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0122.s0 RH1E6S07_0122.rest = RH1E6S07_0122.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0122.s0 :: RH1E6S07_0122.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0122.s0.t = ((30061417348 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0122.s0]
  have e1 : RH1E6S07_0122.sL.t = ((30066089671 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0122.sL]
  rw [e0, e1] at h
  exact h

theorem band_0123 : RS5.BandZeros ((30066089671 : ℝ) / 65536) ((30070757661 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0123.s0 RH1E6S07_0123.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0123.s0 RH1E6S07_0123.rest = RH1E6S07_0123.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0123.s0 :: RH1E6S07_0123.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0123.s0.t = ((30066089671 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0123.s0]
  have e1 : RH1E6S07_0123.sL.t = ((30070757661 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0123.sL]
  rw [e0, e1] at h
  exact h

theorem part_015_1 : RS5.BandZeros ((30061417348 : ℝ) / 65536) ((30070757661 : ℝ) / 65536) 254 := by
  have g0 := band_0122
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0123
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((30061417348 : ℝ) / 65536) ((30070757661 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_015_1 <;> assumption
