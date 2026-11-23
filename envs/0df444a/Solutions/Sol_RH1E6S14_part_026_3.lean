-- Prove2me | solution 1 for RH1E6S14.part_026_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T04:01:53.862254+00:00
-- url     : https://prove2.me/submissions/fb63c874-d560-4940-a337-02afbcf2bba7

import Definitions.Def_RH1E6S14_D026_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0214 : RS5.BandZeros ((53380139748 : ℝ) / 65536) ((53384589759 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0214.s0 RH1E6S14_0214.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0214.s0 RH1E6S14_0214.rest = RH1E6S14_0214.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0214.s0 :: RH1E6S14_0214.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0214.s0.t = ((53380139748 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0214.s0]
  have e1 : RH1E6S14_0214.sL.t = ((53384589759 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0214.sL]
  rw [e0, e1] at h
  exact h

theorem band_0215 : RS5.BandZeros ((53384589759 : ℝ) / 65536) ((53389023591 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0215.s0 RH1E6S14_0215.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0215.s0 RH1E6S14_0215.rest = RH1E6S14_0215.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0215.s0 :: RH1E6S14_0215.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0215.s0.t = ((53384589759 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0215.s0]
  have e1 : RH1E6S14_0215.sL.t = ((53389023591 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0215.sL]
  rw [e0, e1] at h
  exact h

theorem part_026_3 : RS5.BandZeros ((53380139748 : ℝ) / 65536) ((53389023591 : ℝ) / 65536) 254 := by
  have g0 := band_0214
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0215
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((53380139748 : ℝ) / 65536) ((53389023591 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_026_3 <;> assumption
