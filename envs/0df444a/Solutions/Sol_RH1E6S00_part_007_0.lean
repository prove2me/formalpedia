-- Prove2me | solution 1 for RH1E6S00.part_007_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T21:02:37.316188+00:00
-- url     : https://prove2.me/submissions/65c02ef3-f03d-4969-82e0-dba56b477b92

import Definitions.Def_RH1E6S00_D007_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0056 : RS5.BandZeros ((6855600617 : ℝ) / 65536) ((6860991120 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0056.s0 RH1E6S00_0056.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0056.s0 RH1E6S00_0056.rest = RH1E6S00_0056.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0056.s0 :: RH1E6S00_0056.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0056.s0.t = ((6855600617 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0056.s0]
  have e1 : RH1E6S00_0056.sL.t = ((6860991120 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0056.sL]
  rw [e0, e1] at h
  exact h

theorem band_0057 : RS5.BandZeros ((6860991120 : ℝ) / 65536) ((6866370598 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0057.s0 RH1E6S00_0057.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0057.s0 RH1E6S00_0057.rest = RH1E6S00_0057.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0057.s0 :: RH1E6S00_0057.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0057.s0.t = ((6860991120 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0057.s0]
  have e1 : RH1E6S00_0057.sL.t = ((6866370598 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0057.sL]
  rw [e0, e1] at h
  exact h

theorem part_007_0 : RS5.BandZeros ((6855600617 : ℝ) / 65536) ((6866370598 : ℝ) / 65536) 254 := by
  have g0 := band_0056
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0057
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((6855600617 : ℝ) / 65536) ((6866370598 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_007_0 <;> assumption
