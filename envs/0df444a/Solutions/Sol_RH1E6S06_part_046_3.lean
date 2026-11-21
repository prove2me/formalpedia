-- Prove2me | solution 1 for RH1E6S06.part_046_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T19:13:14.57136+00:00
-- url     : https://prove2.me/submissions/9f8986d7-3a2d-415f-a7ed-b0a64599a5ce

import Definitions.Def_RH1E6S06_D046_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0374 : RS5.BandZeros ((27977338591 : ℝ) / 65536) ((27982031058 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0374.s0 RH1E6S06_0374.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0374.s0 RH1E6S06_0374.rest = RH1E6S06_0374.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0374.s0 :: RH1E6S06_0374.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0374.s0.t = ((27977338591 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0374.s0]
  have e1 : RH1E6S06_0374.sL.t = ((27982031058 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0374.sL]
  rw [e0, e1] at h
  exact h

theorem band_0375 : RS5.BandZeros ((27982031058 : ℝ) / 65536) ((27986748827 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0375.s0 RH1E6S06_0375.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0375.s0 RH1E6S06_0375.rest = RH1E6S06_0375.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0375.s0 :: RH1E6S06_0375.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0375.s0.t = ((27982031058 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0375.s0]
  have e1 : RH1E6S06_0375.sL.t = ((27986748827 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0375.sL]
  rw [e0, e1] at h
  exact h

theorem part_046_3 : RS5.BandZeros ((27977338591 : ℝ) / 65536) ((27986748827 : ℝ) / 65536) 254 := by
  have g0 := band_0374
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0375
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((27977338591 : ℝ) / 65536) ((27986748827 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_046_3 <;> assumption
