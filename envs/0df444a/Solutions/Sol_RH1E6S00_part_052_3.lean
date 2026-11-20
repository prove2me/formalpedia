-- Prove2me | solution 1 for RH1E6S00.part_052_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T22:33:44.8747+00:00
-- url     : https://prove2.me/submissions/ea02571f-af32-4099-8119-958806a1e227

import Definitions.Def_RH1E6S00_D052_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0422 : RS5.BandZeros ((8798759144 : ℝ) / 65536) ((8803973475 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0422.s0 RH1E6S00_0422.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0422.s0 RH1E6S00_0422.rest = RH1E6S00_0422.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0422.s0 :: RH1E6S00_0422.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0422.s0.t = ((8798759144 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0422.s0]
  have e1 : RH1E6S00_0422.sL.t = ((8803973475 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0422.sL]
  rw [e0, e1] at h
  exact h

theorem band_0423 : RS5.BandZeros ((8803973475 : ℝ) / 65536) ((8809228794 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0423.s0 RH1E6S00_0423.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0423.s0 RH1E6S00_0423.rest = RH1E6S00_0423.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0423.s0 :: RH1E6S00_0423.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0423.s0.t = ((8803973475 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0423.s0]
  have e1 : RH1E6S00_0423.sL.t = ((8809228794 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0423.sL]
  rw [e0, e1] at h
  exact h

theorem part_052_3 : RS5.BandZeros ((8798759144 : ℝ) / 65536) ((8809228794 : ℝ) / 65536) 254 := by
  have g0 := band_0422
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0423
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((8798759144 : ℝ) / 65536) ((8809228794 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_052_3 <;> assumption
