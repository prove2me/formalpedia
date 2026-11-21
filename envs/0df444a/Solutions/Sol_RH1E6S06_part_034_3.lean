-- Prove2me | solution 1 for RH1E6S06.part_034_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T18:40:59.012003+00:00
-- url     : https://prove2.me/submissions/9426d4d5-e907-4580-b436-beef4342d338

import Definitions.Def_RH1E6S06_D034_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0278 : RS5.BandZeros ((27525797153 : ℝ) / 65536) ((27530518092 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0278.s0 RH1E6S06_0278.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0278.s0 RH1E6S06_0278.rest = RH1E6S06_0278.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0278.s0 :: RH1E6S06_0278.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0278.s0.t = ((27525797153 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0278.s0]
  have e1 : RH1E6S06_0278.sL.t = ((27530518092 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0278.sL]
  rw [e0, e1] at h
  exact h

theorem band_0279 : RS5.BandZeros ((27530518092 : ℝ) / 65536) ((27535223760 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0279.s0 RH1E6S06_0279.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0279.s0 RH1E6S06_0279.rest = RH1E6S06_0279.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0279.s0 :: RH1E6S06_0279.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0279.s0.t = ((27530518092 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0279.s0]
  have e1 : RH1E6S06_0279.sL.t = ((27535223760 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0279.sL]
  rw [e0, e1] at h
  exact h

theorem part_034_3 : RS5.BandZeros ((27525797153 : ℝ) / 65536) ((27535223760 : ℝ) / 65536) 254 := by
  have g0 := band_0278
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0279
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((27525797153 : ℝ) / 65536) ((27535223760 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_034_3 <;> assumption
