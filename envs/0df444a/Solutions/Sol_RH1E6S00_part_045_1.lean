-- Prove2me | solution 1 for RH1E6S00.part_045_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T22:17:28.678175+00:00
-- url     : https://prove2.me/submissions/0d70e9ef-8adf-469b-9544-d4895b381540

import Definitions.Def_RH1E6S00_D045_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0362 : RS5.BandZeros ((8483437075 : ℝ) / 65536) ((8488712009 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0362.s0 RH1E6S00_0362.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0362.s0 RH1E6S00_0362.rest = RH1E6S00_0362.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0362.s0 :: RH1E6S00_0362.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0362.s0.t = ((8483437075 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0362.s0]
  have e1 : RH1E6S00_0362.sL.t = ((8488712009 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0362.sL]
  rw [e0, e1] at h
  exact h

theorem band_0363 : RS5.BandZeros ((8488712009 : ℝ) / 65536) ((8493976250 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0363.s0 RH1E6S00_0363.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0363.s0 RH1E6S00_0363.rest = RH1E6S00_0363.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0363.s0 :: RH1E6S00_0363.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0363.s0.t = ((8488712009 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0363.s0]
  have e1 : RH1E6S00_0363.sL.t = ((8493976250 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0363.sL]
  rw [e0, e1] at h
  exact h

theorem part_045_1 : RS5.BandZeros ((8483437075 : ℝ) / 65536) ((8493976250 : ℝ) / 65536) 254 := by
  have g0 := band_0362
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0363
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((8483437075 : ℝ) / 65536) ((8493976250 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_045_1 <;> assumption
