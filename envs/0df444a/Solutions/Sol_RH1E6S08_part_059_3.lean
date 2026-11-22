-- Prove2me | solution 1 for RH1E6S08.part_059_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T06:49:08.47994+00:00
-- url     : https://prove2.me/submissions/650d6315-fb90-4ab3-af53-5be0b842a476

import Definitions.Def_RH1E6S08_D059_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0478 : RS5.BandZeros ((34976746453 : ℝ) / 65536) ((34981361019 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0478.s0 RH1E6S08_0478.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0478.s0 RH1E6S08_0478.rest = RH1E6S08_0478.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0478.s0 :: RH1E6S08_0478.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0478.s0.t = ((34976746453 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0478.s0]
  have e1 : RH1E6S08_0478.sL.t = ((34981361019 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0478.sL]
  rw [e0, e1] at h
  exact h

theorem band_0479 : RS5.BandZeros ((34981361019 : ℝ) / 65536) ((34985975981 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0479.s0 RH1E6S08_0479.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0479.s0 RH1E6S08_0479.rest = RH1E6S08_0479.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0479.s0 :: RH1E6S08_0479.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0479.s0.t = ((34981361019 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0479.s0]
  have e1 : RH1E6S08_0479.sL.t = ((34985975981 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0479.sL]
  rw [e0, e1] at h
  exact h

theorem part_059_3 : RS5.BandZeros ((34976746453 : ℝ) / 65536) ((34985975981 : ℝ) / 65536) 254 := by
  have g0 := band_0478
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0479
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((34976746453 : ℝ) / 65536) ((34985975981 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_059_3 <;> assumption
