-- Prove2me | solution 1 for RH1E6S09.part_069_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T14:19:01.817083+00:00
-- url     : https://prove2.me/submissions/05771fa0-1df5-4adf-8d0f-fabdd9116cde

import Definitions.Def_RH1E6S09_D069_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0556 : RS5.BandZeros ((38592114433 : ℝ) / 65536) ((38596686184 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0556.s0 RH1E6S09_0556.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0556.s0 RH1E6S09_0556.rest = RH1E6S09_0556.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0556.s0 :: RH1E6S09_0556.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0556.s0.t = ((38592114433 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0556.s0]
  have e1 : RH1E6S09_0556.sL.t = ((38596686184 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0556.sL]
  rw [e0, e1] at h
  exact h

theorem band_0557 : RS5.BandZeros ((38596686184 : ℝ) / 65536) ((38601257798 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0557.s0 RH1E6S09_0557.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0557.s0 RH1E6S09_0557.rest = RH1E6S09_0557.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0557.s0 :: RH1E6S09_0557.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0557.s0.t = ((38596686184 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0557.s0]
  have e1 : RH1E6S09_0557.sL.t = ((38601257798 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0557.sL]
  rw [e0, e1] at h
  exact h

theorem part_069_2 : RS5.BandZeros ((38592114433 : ℝ) / 65536) ((38601257798 : ℝ) / 65536) 254 := by
  have g0 := band_0556
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0557
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((38592114433 : ℝ) / 65536) ((38601257798 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_069_2 <;> assumption
