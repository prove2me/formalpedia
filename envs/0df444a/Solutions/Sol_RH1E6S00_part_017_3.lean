-- Prove2me | solution 1 for RH1E6S00.part_017_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T21:23:47.52272+00:00
-- url     : https://prove2.me/submissions/6f4696db-0775-4b68-85b2-ae9326f1e381

import Definitions.Def_RH1E6S00_D017_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0142 : RS5.BandZeros ((7316730925 : ℝ) / 65536) ((7322075064 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0142.s0 RH1E6S00_0142.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0142.s0 RH1E6S00_0142.rest = RH1E6S00_0142.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0142.s0 :: RH1E6S00_0142.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0142.s0.t = ((7316730925 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0142.s0]
  have e1 : RH1E6S00_0142.sL.t = ((7322075064 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0142.sL]
  rw [e0, e1] at h
  exact h

theorem band_0143 : RS5.BandZeros ((7322075064 : ℝ) / 65536) ((7327418804 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0143.s0 RH1E6S00_0143.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0143.s0 RH1E6S00_0143.rest = RH1E6S00_0143.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0143.s0 :: RH1E6S00_0143.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0143.s0.t = ((7322075064 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0143.s0]
  have e1 : RH1E6S00_0143.sL.t = ((7327418804 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0143.sL]
  rw [e0, e1] at h
  exact h

theorem part_017_3 : RS5.BandZeros ((7316730925 : ℝ) / 65536) ((7327418804 : ℝ) / 65536) 254 := by
  have g0 := band_0142
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0143
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((7316730925 : ℝ) / 65536) ((7327418804 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_017_3 <;> assumption
