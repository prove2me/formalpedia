-- Prove2me | solution 1 for RH1E6S03.part_078_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T08:11:09.407966+00:00
-- url     : https://prove2.me/submissions/810842ad-8aa6-42b6-8e23-a24e0af3dbb2

import Definitions.Def_RH1E6S03_D078_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0626 : RS5.BandZeros ((19449380611 : ℝ) / 65536) ((19454229871 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0626.s0 RH1E6S03_0626.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0626.s0 RH1E6S03_0626.rest = RH1E6S03_0626.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0626.s0 :: RH1E6S03_0626.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0626.s0.t = ((19449380611 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0626.s0]
  have e1 : RH1E6S03_0626.sL.t = ((19454229871 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0626.sL]
  rw [e0, e1] at h
  exact h

theorem band_0627 : RS5.BandZeros ((19454229871 : ℝ) / 65536) ((19459088584 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0627.s0 RH1E6S03_0627.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0627.s0 RH1E6S03_0627.rest = RH1E6S03_0627.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0627.s0 :: RH1E6S03_0627.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0627.s0.t = ((19454229871 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0627.s0]
  have e1 : RH1E6S03_0627.sL.t = ((19459088584 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0627.sL]
  rw [e0, e1] at h
  exact h

theorem part_078_1 : RS5.BandZeros ((19449380611 : ℝ) / 65536) ((19459088584 : ℝ) / 65536) 254 := by
  have g0 := band_0626
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0627
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((19449380611 : ℝ) / 65536) ((19459088584 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_078_1 <;> assumption
