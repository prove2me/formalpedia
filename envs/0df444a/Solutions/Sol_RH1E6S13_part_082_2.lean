-- Prove2me | solution 1 for RH1E6S13.part_082_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T01:50:15.791597+00:00
-- url     : https://prove2.me/submissions/cc34635e-2791-442e-8289-fe93d003029e

import Definitions.Def_RH1E6S13_D082_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0660 : RS5.BandZeros ((52097119781 : ℝ) / 65536) ((52101588666 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0660.s0 RH1E6S13_0660.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0660.s0 RH1E6S13_0660.rest = RH1E6S13_0660.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0660.s0 :: RH1E6S13_0660.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0660.s0.t = ((52097119781 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0660.s0]
  have e1 : RH1E6S13_0660.sL.t = ((52101588666 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0660.sL]
  rw [e0, e1] at h
  exact h

theorem band_0661 : RS5.BandZeros ((52101588666 : ℝ) / 65536) ((52106031230 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0661.s0 RH1E6S13_0661.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0661.s0 RH1E6S13_0661.rest = RH1E6S13_0661.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0661.s0 :: RH1E6S13_0661.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0661.s0.t = ((52101588666 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0661.s0]
  have e1 : RH1E6S13_0661.sL.t = ((52106031230 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0661.sL]
  rw [e0, e1] at h
  exact h

theorem part_082_2 : RS5.BandZeros ((52097119781 : ℝ) / 65536) ((52106031230 : ℝ) / 65536) 254 := by
  have g0 := band_0660
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0661
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((52097119781 : ℝ) / 65536) ((52106031230 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_082_2 <;> assumption
