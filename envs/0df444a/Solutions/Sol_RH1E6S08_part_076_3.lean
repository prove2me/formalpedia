-- Prove2me | solution 1 for RH1E6S08.part_076_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T07:36:06.845684+00:00
-- url     : https://prove2.me/submissions/8f578554-767c-493e-9ce2-25924ba2c4df

import Definitions.Def_RH1E6S08_D076_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0614 : RS5.BandZeros ((35602907747 : ℝ) / 65536) ((35607503986 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0614.s0 RH1E6S08_0614.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0614.s0 RH1E6S08_0614.rest = RH1E6S08_0614.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0614.s0 :: RH1E6S08_0614.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0614.s0.t = ((35602907747 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0614.s0]
  have e1 : RH1E6S08_0614.sL.t = ((35607503986 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0614.sL]
  rw [e0, e1] at h
  exact h

theorem band_0615 : RS5.BandZeros ((35607503986 : ℝ) / 65536) ((35612104283 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0615.s0 RH1E6S08_0615.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0615.s0 RH1E6S08_0615.rest = RH1E6S08_0615.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0615.s0 :: RH1E6S08_0615.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0615.s0.t = ((35607503986 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0615.s0]
  have e1 : RH1E6S08_0615.sL.t = ((35612104283 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0615.sL]
  rw [e0, e1] at h
  exact h

theorem part_076_3 : RS5.BandZeros ((35602907747 : ℝ) / 65536) ((35612104283 : ℝ) / 65536) 254 := by
  have g0 := band_0614
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0615
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((35602907747 : ℝ) / 65536) ((35612104283 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_076_3 <;> assumption
