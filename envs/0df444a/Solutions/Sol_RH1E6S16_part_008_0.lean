-- Prove2me | solution 1 for RH1E6S16.part_008_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T14:23:29.751564+00:00
-- url     : https://prove2.me/submissions/5e8295db-09ef-4ae5-ade2-f29cc609321b

import Definitions.Def_RH1E6S16_D008_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0064 : RS5.BandZeros ((59264242340 : ℝ) / 65536) ((59268634988 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0064.s0 RH1E6S16_0064.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0064.s0 RH1E6S16_0064.rest = RH1E6S16_0064.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0064.s0 :: RH1E6S16_0064.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0064.s0.t = ((59264242340 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0064.s0]
  have e1 : RH1E6S16_0064.sL.t = ((59268634988 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0064.sL]
  rw [e0, e1] at h
  exact h

theorem band_0065 : RS5.BandZeros ((59268634988 : ℝ) / 65536) ((59273057185 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0065.s0 RH1E6S16_0065.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0065.s0 RH1E6S16_0065.rest = RH1E6S16_0065.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0065.s0 :: RH1E6S16_0065.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0065.s0.t = ((59268634988 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0065.s0]
  have e1 : RH1E6S16_0065.sL.t = ((59273057185 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0065.sL]
  rw [e0, e1] at h
  exact h

theorem part_008_0 : RS5.BandZeros ((59264242340 : ℝ) / 65536) ((59273057185 : ℝ) / 65536) 254 := by
  have g0 := band_0064
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0065
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((59264242340 : ℝ) / 65536) ((59273057185 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_008_0 <;> assumption
