-- Prove2me | solution 1 for RH1E6S01.part_046_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T00:57:38.07818+00:00
-- url     : https://prove2.me/submissions/fa25b51d-4b97-4737-be52-b6ac36ac1444

import Definitions.Def_RH1E6S01_D046_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0374 : RS5.BandZeros ((11753097233 : ℝ) / 65536) ((11758174498 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0374.s0 RH1E6S01_0374.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0374.s0 RH1E6S01_0374.rest = RH1E6S01_0374.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0374.s0 :: RH1E6S01_0374.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0374.s0.t = ((11753097233 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0374.s0]
  have e1 : RH1E6S01_0374.sL.t = ((11758174498 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0374.sL]
  rw [e0, e1] at h
  exact h

theorem band_0375 : RS5.BandZeros ((11758174498 : ℝ) / 65536) ((11763291682 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0375.s0 RH1E6S01_0375.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0375.s0 RH1E6S01_0375.rest = RH1E6S01_0375.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0375.s0 :: RH1E6S01_0375.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0375.s0.t = ((11758174498 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0375.s0]
  have e1 : RH1E6S01_0375.sL.t = ((11763291682 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0375.sL]
  rw [e0, e1] at h
  exact h

theorem part_046_3 : RS5.BandZeros ((11753097233 : ℝ) / 65536) ((11763291682 : ℝ) / 65536) 254 := by
  have g0 := band_0374
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0375
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((11753097233 : ℝ) / 65536) ((11763291682 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_046_3 <;> assumption
