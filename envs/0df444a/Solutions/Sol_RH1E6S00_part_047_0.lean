-- Prove2me | solution 1 for RH1E6S00.part_047_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T22:22:03.136763+00:00
-- url     : https://prove2.me/submissions/e44a89a7-3646-45f5-b5fa-c1ec9ec0257c

import Definitions.Def_RH1E6S00_D047_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0376 : RS5.BandZeros ((8557131966 : ℝ) / 65536) ((8562391958 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0376.s0 RH1E6S00_0376.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0376.s0 RH1E6S00_0376.rest = RH1E6S00_0376.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0376.s0 :: RH1E6S00_0376.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0376.s0.t = ((8557131966 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0376.s0]
  have e1 : RH1E6S00_0376.sL.t = ((8562391958 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0376.sL]
  rw [e0, e1] at h
  exact h

theorem band_0377 : RS5.BandZeros ((8562391958 : ℝ) / 65536) ((8567641272 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0377.s0 RH1E6S00_0377.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0377.s0 RH1E6S00_0377.rest = RH1E6S00_0377.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0377.s0 :: RH1E6S00_0377.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0377.s0.t = ((8562391958 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0377.s0]
  have e1 : RH1E6S00_0377.sL.t = ((8567641272 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0377.sL]
  rw [e0, e1] at h
  exact h

theorem part_047_0 : RS5.BandZeros ((8557131966 : ℝ) / 65536) ((8567641272 : ℝ) / 65536) 254 := by
  have g0 := band_0376
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0377
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((8557131966 : ℝ) / 65536) ((8567641272 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_047_0 <;> assumption
