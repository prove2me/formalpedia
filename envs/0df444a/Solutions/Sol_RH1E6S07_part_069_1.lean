-- Prove2me | solution 1 for RH1E6S07.part_069_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T02:10:18.915103+00:00
-- url     : https://prove2.me/submissions/e7141d37-ea2e-4ff3-b208-bd45051c8e1d

import Definitions.Def_RH1E6S07_D069_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0554 : RS5.BandZeros ((32072953376 : ℝ) / 65536) ((32077588460 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0554.s0 RH1E6S07_0554.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0554.s0 RH1E6S07_0554.rest = RH1E6S07_0554.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0554.s0 :: RH1E6S07_0554.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0554.s0.t = ((32072953376 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0554.s0]
  have e1 : RH1E6S07_0554.sL.t = ((32077588460 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0554.sL]
  rw [e0, e1] at h
  exact h

theorem band_0555 : RS5.BandZeros ((32077588460 : ℝ) / 65536) ((32082242727 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0555.s0 RH1E6S07_0555.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0555.s0 RH1E6S07_0555.rest = RH1E6S07_0555.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0555.s0 :: RH1E6S07_0555.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0555.s0.t = ((32077588460 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0555.s0]
  have e1 : RH1E6S07_0555.sL.t = ((32082242727 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0555.sL]
  rw [e0, e1] at h
  exact h

theorem part_069_1 : RS5.BandZeros ((32072953376 : ℝ) / 65536) ((32082242727 : ℝ) / 65536) 254 := by
  have g0 := band_0554
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0555
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((32072953376 : ℝ) / 65536) ((32082242727 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_069_1 <;> assumption
