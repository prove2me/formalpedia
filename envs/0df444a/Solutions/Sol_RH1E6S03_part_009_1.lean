-- Prove2me | solution 1 for RH1E6S03.part_009_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T05:41:10.216529+00:00
-- url     : https://prove2.me/submissions/2275f28e-c106-4edb-8080-20f3de68ff08

import Definitions.Def_RH1E6S03_D009_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0074 : RS5.BandZeros ((16748993435 : ℝ) / 65536) ((16753930379 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0074.s0 RH1E6S03_0074.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0074.s0 RH1E6S03_0074.rest = RH1E6S03_0074.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0074.s0 :: RH1E6S03_0074.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0074.s0.t = ((16748993435 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0074.s0]
  have e1 : RH1E6S03_0074.sL.t = ((16753930379 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0074.sL]
  rw [e0, e1] at h
  exact h

theorem band_0075 : RS5.BandZeros ((16753930379 : ℝ) / 65536) ((16758847788 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0075.s0 RH1E6S03_0075.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0075.s0 RH1E6S03_0075.rest = RH1E6S03_0075.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0075.s0 :: RH1E6S03_0075.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0075.s0.t = ((16753930379 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0075.s0]
  have e1 : RH1E6S03_0075.sL.t = ((16758847788 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0075.sL]
  rw [e0, e1] at h
  exact h

theorem part_009_1 : RS5.BandZeros ((16748993435 : ℝ) / 65536) ((16758847788 : ℝ) / 65536) 254 := by
  have g0 := band_0074
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0075
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((16748993435 : ℝ) / 65536) ((16758847788 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_009_1 <;> assumption
