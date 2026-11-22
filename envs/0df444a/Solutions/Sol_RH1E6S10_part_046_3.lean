-- Prove2me | solution 1 for RH1E6S10.part_046_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T01:03:04.689883+00:00
-- url     : https://prove2.me/submissions/4503d53e-2eec-40cf-94f2-232760558f73

import Definitions.Def_RH1E6S10_D046_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0374 : RS5.BandZeros ((41024122098 : ℝ) / 65536) ((41028665870 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0374.s0 RH1E6S10_0374.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0374.s0 RH1E6S10_0374.rest = RH1E6S10_0374.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0374.s0 :: RH1E6S10_0374.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0374.s0.t = ((41024122098 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0374.s0]
  have e1 : RH1E6S10_0374.sL.t = ((41028665870 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0374.sL]
  rw [e0, e1] at h
  exact h

theorem band_0375 : RS5.BandZeros ((41028665870 : ℝ) / 65536) ((41033200654 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0375.s0 RH1E6S10_0375.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0375.s0 RH1E6S10_0375.rest = RH1E6S10_0375.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0375.s0 :: RH1E6S10_0375.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0375.s0.t = ((41028665870 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0375.s0]
  have e1 : RH1E6S10_0375.sL.t = ((41033200654 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0375.sL]
  rw [e0, e1] at h
  exact h

theorem part_046_3 : RS5.BandZeros ((41024122098 : ℝ) / 65536) ((41033200654 : ℝ) / 65536) 254 := by
  have g0 := band_0374
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0375
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((41024122098 : ℝ) / 65536) ((41033200654 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_046_3 <;> assumption
