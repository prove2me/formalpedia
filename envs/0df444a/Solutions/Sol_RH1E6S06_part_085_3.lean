-- Prove2me | solution 1 for RH1E6S06.part_085_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T22:46:33.84823+00:00
-- url     : https://prove2.me/submissions/db73cedb-ae01-4b37-9444-223fb20f452b

import Definitions.Def_RH1E6S06_D085_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0686 : RS5.BandZeros ((29440395284 : ℝ) / 65536) ((29445087314 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0686.s0 RH1E6S06_0686.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0686.s0 RH1E6S06_0686.rest = RH1E6S06_0686.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0686.s0 :: RH1E6S06_0686.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0686.s0.t = ((29440395284 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0686.s0]
  have e1 : RH1E6S06_0686.sL.t = ((29445087314 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0686.sL]
  rw [e0, e1] at h
  exact h

theorem band_0687 : RS5.BandZeros ((29445087314 : ℝ) / 65536) ((29449747924 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0687.s0 RH1E6S06_0687.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0687.s0 RH1E6S06_0687.rest = RH1E6S06_0687.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0687.s0 :: RH1E6S06_0687.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0687.s0.t = ((29445087314 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0687.s0]
  have e1 : RH1E6S06_0687.sL.t = ((29449747924 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0687.sL]
  rw [e0, e1] at h
  exact h

theorem part_085_3 : RS5.BandZeros ((29440395284 : ℝ) / 65536) ((29449747924 : ℝ) / 65536) 254 := by
  have g0 := band_0686
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0687
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((29440395284 : ℝ) / 65536) ((29449747924 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_085_3 <;> assumption
