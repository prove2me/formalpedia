-- Prove2me | solution 1 for RH1E6S00.part_006_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T21:02:31.312183+00:00
-- url     : https://prove2.me/submissions/88b8fdce-7550-4990-8322-8e038fc7b1b0

import Definitions.Def_RH1E6S00_D006_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0050 : RS5.BandZeros ((6823301404 : ℝ) / 65536) ((6828683931 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0050.s0 RH1E6S00_0050.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0050.s0 RH1E6S00_0050.rest = RH1E6S00_0050.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0050.s0 :: RH1E6S00_0050.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0050.s0.t = ((6823301404 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0050.s0]
  have e1 : RH1E6S00_0050.sL.t = ((6828683931 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0050.sL]
  rw [e0, e1] at h
  exact h

theorem band_0051 : RS5.BandZeros ((6828683931 : ℝ) / 65536) ((6834076616 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0051.s0 RH1E6S00_0051.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0051.s0 RH1E6S00_0051.rest = RH1E6S00_0051.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0051.s0 :: RH1E6S00_0051.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0051.s0.t = ((6828683931 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0051.s0]
  have e1 : RH1E6S00_0051.sL.t = ((6834076616 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0051.sL]
  rw [e0, e1] at h
  exact h

theorem part_006_1 : RS5.BandZeros ((6823301404 : ℝ) / 65536) ((6834076616 : ℝ) / 65536) 254 := by
  have g0 := band_0050
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0051
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((6823301404 : ℝ) / 65536) ((6834076616 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_006_1 <;> assumption
