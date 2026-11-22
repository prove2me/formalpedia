-- Prove2me | solution 1 for RH1E6S13.part_045_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T23:12:54.120305+00:00
-- url     : https://prove2.me/submissions/28465cd3-ab28-483b-b25c-5614d8b006eb

import Definitions.Def_RH1E6S13_D045_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0366 : RS5.BandZeros ((50787018715 : ℝ) / 65536) ((50791488526 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0366.s0 RH1E6S13_0366.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0366.s0 RH1E6S13_0366.rest = RH1E6S13_0366.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0366.s0 :: RH1E6S13_0366.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0366.s0.t = ((50787018715 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0366.s0]
  have e1 : RH1E6S13_0366.sL.t = ((50791488526 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0366.sL]
  rw [e0, e1] at h
  exact h

theorem band_0367 : RS5.BandZeros ((50791488526 : ℝ) / 65536) ((50795931960 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0367.s0 RH1E6S13_0367.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0367.s0 RH1E6S13_0367.rest = RH1E6S13_0367.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0367.s0 :: RH1E6S13_0367.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0367.s0.t = ((50791488526 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0367.s0]
  have e1 : RH1E6S13_0367.sL.t = ((50795931960 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0367.sL]
  rw [e0, e1] at h
  exact h

theorem part_045_3 : RS5.BandZeros ((50787018715 : ℝ) / 65536) ((50795931960 : ℝ) / 65536) 254 := by
  have g0 := band_0366
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0367
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((50787018715 : ℝ) / 65536) ((50795931960 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_045_3 <;> assumption
