-- Prove2me | solution 1 for RH1E6S02.part_003_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T02:15:21.514179+00:00
-- url     : https://prove2.me/submissions/d839d758-d18d-4a52-af23-888b7d38e0f9

import Definitions.Def_RH1E6S02_D003_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0026 : RS5.BandZeros ((13238285686 : ℝ) / 65536) ((13243320791 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0026.s0 RH1E6S02_0026.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0026.s0 RH1E6S02_0026.rest = RH1E6S02_0026.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0026.s0 :: RH1E6S02_0026.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0026.s0.t = ((13238285686 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0026.s0]
  have e1 : RH1E6S02_0026.sL.t = ((13243320791 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0026.sL]
  rw [e0, e1] at h
  exact h

theorem band_0027 : RS5.BandZeros ((13243320791 : ℝ) / 65536) ((13248362729 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0027.s0 RH1E6S02_0027.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0027.s0 RH1E6S02_0027.rest = RH1E6S02_0027.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0027.s0 :: RH1E6S02_0027.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0027.s0.t = ((13243320791 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0027.s0]
  have e1 : RH1E6S02_0027.sL.t = ((13248362729 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0027.sL]
  rw [e0, e1] at h
  exact h

theorem part_003_1 : RS5.BandZeros ((13238285686 : ℝ) / 65536) ((13248362729 : ℝ) / 65536) 254 := by
  have g0 := band_0026
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0027
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((13238285686 : ℝ) / 65536) ((13248362729 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_003_1 <;> assumption
