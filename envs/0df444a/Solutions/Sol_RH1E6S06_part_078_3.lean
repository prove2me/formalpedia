-- Prove2me | solution 1 for RH1E6S06.part_078_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T22:25:29.271554+00:00
-- url     : https://prove2.me/submissions/7ad58726-d888-40a3-b977-63e607e91706

import Definitions.Def_RH1E6S06_D078_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0630 : RS5.BandZeros ((29178289097 : ℝ) / 65536) ((29182972881 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0630.s0 RH1E6S06_0630.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0630.s0 RH1E6S06_0630.rest = RH1E6S06_0630.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0630.s0 :: RH1E6S06_0630.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0630.s0.t = ((29178289097 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0630.s0]
  have e1 : RH1E6S06_0630.sL.t = ((29182972881 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0630.sL]
  rw [e0, e1] at h
  exact h

theorem band_0631 : RS5.BandZeros ((29182972881 : ℝ) / 65536) ((29187668213 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0631.s0 RH1E6S06_0631.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0631.s0 RH1E6S06_0631.rest = RH1E6S06_0631.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0631.s0 :: RH1E6S06_0631.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0631.s0.t = ((29182972881 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0631.s0]
  have e1 : RH1E6S06_0631.sL.t = ((29187668213 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0631.sL]
  rw [e0, e1] at h
  exact h

theorem part_078_3 : RS5.BandZeros ((29178289097 : ℝ) / 65536) ((29187668213 : ℝ) / 65536) 254 := by
  have g0 := band_0630
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0631
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((29178289097 : ℝ) / 65536) ((29187668213 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_078_3 <;> assumption
