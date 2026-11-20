-- Prove2me | solution 1 for RH1E6S02.part_020_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T02:51:13.003392+00:00
-- url     : https://prove2.me/submissions/f6dde209-c1f6-4e90-8c14-f4e38417a5bd

import Definitions.Def_RH1E6S02_D020_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0160 : RS5.BandZeros ((13911892971 : ℝ) / 65536) ((13916899315 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0160.s0 RH1E6S02_0160.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0160.s0 RH1E6S02_0160.rest = RH1E6S02_0160.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0160.s0 :: RH1E6S02_0160.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0160.s0.t = ((13911892971 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0160.s0]
  have e1 : RH1E6S02_0160.sL.t = ((13916899315 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0160.sL]
  rw [e0, e1] at h
  exact h

theorem band_0161 : RS5.BandZeros ((13916899315 : ℝ) / 65536) ((13921909218 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0161.s0 RH1E6S02_0161.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0161.s0 RH1E6S02_0161.rest = RH1E6S02_0161.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0161.s0 :: RH1E6S02_0161.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0161.s0.t = ((13916899315 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0161.s0]
  have e1 : RH1E6S02_0161.sL.t = ((13921909218 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0161.sL]
  rw [e0, e1] at h
  exact h

theorem part_020_0 : RS5.BandZeros ((13911892971 : ℝ) / 65536) ((13921909218 : ℝ) / 65536) 254 := by
  have g0 := band_0160
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0161
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((13911892971 : ℝ) / 65536) ((13921909218 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_020_0 <;> assumption
