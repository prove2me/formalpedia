-- Prove2me | solution 1 for RH1E6S04.part_022_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T09:13:09.722568+00:00
-- url     : https://prove2.me/submissions/dfea743f-3e34-4f30-9ba7-3e31bc2504f2

import Definitions.Def_RH1E6S04_D022_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0176 : RS5.BandZeros ((20513420890 : ℝ) / 65536) ((20518255791 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0176.s0 RH1E6S04_0176.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0176.s0 RH1E6S04_0176.rest = RH1E6S04_0176.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0176.s0 :: RH1E6S04_0176.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0176.s0.t = ((20513420890 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0176.s0]
  have e1 : RH1E6S04_0176.sL.t = ((20518255791 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0176.sL]
  rw [e0, e1] at h
  exact h

theorem band_0177 : RS5.BandZeros ((20518255791 : ℝ) / 65536) ((20523090586 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0177.s0 RH1E6S04_0177.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0177.s0 RH1E6S04_0177.rest = RH1E6S04_0177.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0177.s0 :: RH1E6S04_0177.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0177.s0.t = ((20518255791 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0177.s0]
  have e1 : RH1E6S04_0177.sL.t = ((20523090586 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0177.sL]
  rw [e0, e1] at h
  exact h

theorem part_022_0 : RS5.BandZeros ((20513420890 : ℝ) / 65536) ((20523090586 : ℝ) / 65536) 254 := by
  have g0 := band_0176
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0177
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((20513420890 : ℝ) / 65536) ((20523090586 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_022_0 <;> assumption
