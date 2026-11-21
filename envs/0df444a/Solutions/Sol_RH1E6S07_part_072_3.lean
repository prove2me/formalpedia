-- Prove2me | solution 1 for RH1E6S07.part_072_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T02:19:00.641354+00:00
-- url     : https://prove2.me/submissions/4c45bfcd-edb8-4f13-b9fb-aaf378932d60

import Definitions.Def_RH1E6S07_D072_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0582 : RS5.BandZeros ((32202939098 : ℝ) / 65536) ((32207581349 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0582.s0 RH1E6S07_0582.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0582.s0 RH1E6S07_0582.rest = RH1E6S07_0582.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0582.s0 :: RH1E6S07_0582.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0582.s0.t = ((32202939098 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0582.s0]
  have e1 : RH1E6S07_0582.sL.t = ((32207581349 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0582.sL]
  rw [e0, e1] at h
  exact h

theorem band_0583 : RS5.BandZeros ((32207581349 : ℝ) / 65536) ((32212225829 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0583.s0 RH1E6S07_0583.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0583.s0 RH1E6S07_0583.rest = RH1E6S07_0583.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0583.s0 :: RH1E6S07_0583.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0583.s0.t = ((32207581349 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0583.s0]
  have e1 : RH1E6S07_0583.sL.t = ((32212225829 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0583.sL]
  rw [e0, e1] at h
  exact h

theorem part_072_3 : RS5.BandZeros ((32202939098 : ℝ) / 65536) ((32212225829 : ℝ) / 65536) 254 := by
  have g0 := band_0582
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0583
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((32202939098 : ℝ) / 65536) ((32212225829 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_072_3 <;> assumption
