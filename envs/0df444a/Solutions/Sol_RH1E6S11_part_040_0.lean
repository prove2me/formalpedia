-- Prove2me | solution 1 for RH1E6S11.part_040_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T04:53:44.439416+00:00
-- url     : https://prove2.me/submissions/16500da5-aa1a-48b7-93a5-f38f78532a2d

import Definitions.Def_RH1E6S11_D040_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0320 : RS5.BandZeros ((44045563904 : ℝ) / 65536) ((44050088684 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0320.s0 RH1E6S11_0320.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0320.s0 RH1E6S11_0320.rest = RH1E6S11_0320.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0320.s0 :: RH1E6S11_0320.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0320.s0.t = ((44045563904 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0320.s0]
  have e1 : RH1E6S11_0320.sL.t = ((44050088684 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0320.sL]
  rw [e0, e1] at h
  exact h

theorem band_0321 : RS5.BandZeros ((44050088684 : ℝ) / 65536) ((44054595644 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0321.s0 RH1E6S11_0321.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0321.s0 RH1E6S11_0321.rest = RH1E6S11_0321.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0321.s0 :: RH1E6S11_0321.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0321.s0.t = ((44050088684 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0321.s0]
  have e1 : RH1E6S11_0321.sL.t = ((44054595644 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0321.sL]
  rw [e0, e1] at h
  exact h

theorem part_040_0 : RS5.BandZeros ((44045563904 : ℝ) / 65536) ((44054595644 : ℝ) / 65536) 254 := by
  have g0 := band_0320
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0321
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((44045563904 : ℝ) / 65536) ((44054595644 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_040_0 <;> assumption
