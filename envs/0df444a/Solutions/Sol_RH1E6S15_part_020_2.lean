-- Prove2me | solution 1 for RH1E6S15.part_020_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T09:03:33.508858+00:00
-- url     : https://prove2.me/submissions/9a29a7f1-dee8-46f8-9fd4-12570f067440

import Definitions.Def_RH1E6S15_D020_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0164 : RS5.BandZeros ((56431057050 : ℝ) / 65536) ((56435475607 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0164.s0 RH1E6S15_0164.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0164.s0 RH1E6S15_0164.rest = RH1E6S15_0164.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0164.s0 :: RH1E6S15_0164.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0164.s0.t = ((56431057050 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0164.s0]
  have e1 : RH1E6S15_0164.sL.t = ((56435475607 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0164.sL]
  rw [e0, e1] at h
  exact h

theorem band_0165 : RS5.BandZeros ((56435475607 : ℝ) / 65536) ((56439915114 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0165.s0 RH1E6S15_0165.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0165.s0 RH1E6S15_0165.rest = RH1E6S15_0165.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0165.s0 :: RH1E6S15_0165.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0165.s0.t = ((56435475607 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0165.s0]
  have e1 : RH1E6S15_0165.sL.t = ((56439915114 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0165.sL]
  rw [e0, e1] at h
  exact h

theorem part_020_2 : RS5.BandZeros ((56431057050 : ℝ) / 65536) ((56439915114 : ℝ) / 65536) 254 := by
  have g0 := band_0164
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0165
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((56431057050 : ℝ) / 65536) ((56439915114 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_020_2 <;> assumption
