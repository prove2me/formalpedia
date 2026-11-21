-- Prove2me | solution 1 for RH1E6S07.part_000_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T22:50:27.268194+00:00
-- url     : https://prove2.me/submissions/008ca64e-47ad-486f-8db0-581971376d90

import Definitions.Def_RH1E6S07_D000_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0002 : RS5.BandZeros ((29500553596 : ℝ) / 65536) ((29505229039 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0002.s0 RH1E6S07_0002.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0002.s0 RH1E6S07_0002.rest = RH1E6S07_0002.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0002.s0 :: RH1E6S07_0002.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0002.s0.t = ((29500553596 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0002.s0]
  have e1 : RH1E6S07_0002.sL.t = ((29505229039 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0002.sL]
  rw [e0, e1] at h
  exact h

theorem band_0003 : RS5.BandZeros ((29505229039 : ℝ) / 65536) ((29509904380 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0003.s0 RH1E6S07_0003.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0003.s0 RH1E6S07_0003.rest = RH1E6S07_0003.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0003.s0 :: RH1E6S07_0003.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0003.s0.t = ((29505229039 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0003.s0]
  have e1 : RH1E6S07_0003.sL.t = ((29509904380 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0003.sL]
  rw [e0, e1] at h
  exact h

theorem part_000_1 : RS5.BandZeros ((29500553596 : ℝ) / 65536) ((29509904380 : ℝ) / 65536) 254 := by
  have g0 := band_0002
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0003
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((29500553596 : ℝ) / 65536) ((29509904380 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_000_1 <;> assumption
