-- Prove2me | solution 1 for RH1E6S08.part_088_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T08:09:05.982035+00:00
-- url     : https://prove2.me/submissions/e75e83bd-28bb-4f3d-a2db-9e525f6195a3

import Definitions.Def_RH1E6S08_D088_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0710 : RS5.BandZeros ((36044302248 : ℝ) / 65536) ((36044800000 : ℝ) / 65536) 13 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0710.s0 RH1E6S08_0710.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0710.s0 RH1E6S08_0710.rest = RH1E6S08_0710.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0710.s0 :: RH1E6S08_0710.rest) = 13 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0710.s0.t = ((36044302248 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0710.s0]
  have e1 : RH1E6S08_0710.sL.t = ((36044800000 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0710.sL]
  rw [e0, e1] at h
  exact h

theorem part_088_3 : RS5.BandZeros ((36044302248 : ℝ) / 65536) ((36044800000 : ℝ) / 65536) 13 := by
  exact band_0710

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((36044302248 : ℝ) / 65536) ((36044800000 : ℝ) / 65536) 13 := by
  apply RH1E6S08.part_088_3 <;> assumption
