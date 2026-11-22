-- Prove2me | solution 1 for RH1E6S09.part_060_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T10:56:05.286185+00:00
-- url     : https://prove2.me/submissions/acef6e34-7542-4f62-9496-1975669ca6b1

import Definitions.Def_RH1E6S09_D060_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0480 : RS5.BandZeros ((38244823030 : ℝ) / 65536) ((38249384156 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0480.s0 RH1E6S09_0480.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0480.s0 RH1E6S09_0480.rest = RH1E6S09_0480.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0480.s0 :: RH1E6S09_0480.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0480.s0.t = ((38244823030 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0480.s0]
  have e1 : RH1E6S09_0480.sL.t = ((38249384156 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0480.sL]
  rw [e0, e1] at h
  exact h

theorem band_0481 : RS5.BandZeros ((38249384156 : ℝ) / 65536) ((38253966976 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0481.s0 RH1E6S09_0481.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0481.s0 RH1E6S09_0481.rest = RH1E6S09_0481.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0481.s0 :: RH1E6S09_0481.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0481.s0.t = ((38249384156 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0481.s0]
  have e1 : RH1E6S09_0481.sL.t = ((38253966976 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0481.sL]
  rw [e0, e1] at h
  exact h

theorem part_060_0 : RS5.BandZeros ((38244823030 : ℝ) / 65536) ((38253966976 : ℝ) / 65536) 254 := by
  have g0 := band_0480
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0481
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((38244823030 : ℝ) / 65536) ((38253966976 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_060_0 <;> assumption
