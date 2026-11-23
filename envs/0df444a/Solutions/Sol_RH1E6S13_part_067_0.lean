-- Prove2me | solution 1 for RH1E6S13.part_067_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T00:47:50.01268+00:00
-- url     : https://prove2.me/submissions/5c41507b-c273-4c63-85f6-792cd529b10c

import Definitions.Def_RH1E6S13_D067_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0536 : RS5.BandZeros ((51544925467 : ℝ) / 65536) ((51549372097 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0536.s0 RH1E6S13_0536.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0536.s0 RH1E6S13_0536.rest = RH1E6S13_0536.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0536.s0 :: RH1E6S13_0536.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0536.s0.t = ((51544925467 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0536.s0]
  have e1 : RH1E6S13_0536.sL.t = ((51549372097 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0536.sL]
  rw [e0, e1] at h
  exact h

theorem band_0537 : RS5.BandZeros ((51549372097 : ℝ) / 65536) ((51553836236 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0537.s0 RH1E6S13_0537.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0537.s0 RH1E6S13_0537.rest = RH1E6S13_0537.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0537.s0 :: RH1E6S13_0537.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0537.s0.t = ((51549372097 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0537.s0]
  have e1 : RH1E6S13_0537.sL.t = ((51553836236 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0537.sL]
  rw [e0, e1] at h
  exact h

theorem part_067_0 : RS5.BandZeros ((51544925467 : ℝ) / 65536) ((51553836236 : ℝ) / 65536) 254 := by
  have g0 := band_0536
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0537
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((51544925467 : ℝ) / 65536) ((51553836236 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_067_0 <;> assumption
