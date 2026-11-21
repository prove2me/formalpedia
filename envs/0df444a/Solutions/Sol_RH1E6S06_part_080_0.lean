-- Prove2me | solution 1 for RH1E6S06.part_080_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T22:32:02.650773+00:00
-- url     : https://prove2.me/submissions/db248880-a9aa-41af-ba10-21b569641484

import Definitions.Def_RH1E6S06_D080_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0640 : RS5.BandZeros ((29225128358 : ℝ) / 65536) ((29229782423 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0640.s0 RH1E6S06_0640.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0640.s0 RH1E6S06_0640.rest = RH1E6S06_0640.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0640.s0 :: RH1E6S06_0640.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0640.s0.t = ((29225128358 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0640.s0]
  have e1 : RH1E6S06_0640.sL.t = ((29229782423 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0640.sL]
  rw [e0, e1] at h
  exact h

theorem band_0641 : RS5.BandZeros ((29229782423 : ℝ) / 65536) ((29234473285 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0641.s0 RH1E6S06_0641.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0641.s0 RH1E6S06_0641.rest = RH1E6S06_0641.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0641.s0 :: RH1E6S06_0641.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0641.s0.t = ((29229782423 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0641.s0]
  have e1 : RH1E6S06_0641.sL.t = ((29234473285 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0641.sL]
  rw [e0, e1] at h
  exact h

theorem part_080_0 : RS5.BandZeros ((29225128358 : ℝ) / 65536) ((29234473285 : ℝ) / 65536) 254 := by
  have g0 := band_0640
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0641
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((29225128358 : ℝ) / 65536) ((29234473285 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_080_0 <;> assumption
