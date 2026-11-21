-- Prove2me | solution 1 for RH1E6S03.part_037_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T06:37:46.037074+00:00
-- url     : https://prove2.me/submissions/cc8468c6-6ef0-43b1-a019-dcf49eaff968

import Definitions.Def_RH1E6S03_D037_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0298 : RS5.BandZeros ((17849387585 : ℝ) / 65536) ((17854295111 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0298.s0 RH1E6S03_0298.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0298.s0 RH1E6S03_0298.rest = RH1E6S03_0298.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0298.s0 :: RH1E6S03_0298.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0298.s0.t = ((17849387585 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0298.s0]
  have e1 : RH1E6S03_0298.sL.t = ((17854295111 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0298.sL]
  rw [e0, e1] at h
  exact h

theorem band_0299 : RS5.BandZeros ((17854295111 : ℝ) / 65536) ((17859173588 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0299.s0 RH1E6S03_0299.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0299.s0 RH1E6S03_0299.rest = RH1E6S03_0299.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0299.s0 :: RH1E6S03_0299.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0299.s0.t = ((17854295111 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0299.s0]
  have e1 : RH1E6S03_0299.sL.t = ((17859173588 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0299.sL]
  rw [e0, e1] at h
  exact h

theorem part_037_1 : RS5.BandZeros ((17849387585 : ℝ) / 65536) ((17859173588 : ℝ) / 65536) 254 := by
  have g0 := band_0298
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0299
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((17849387585 : ℝ) / 65536) ((17859173588 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_037_1 <;> assumption
