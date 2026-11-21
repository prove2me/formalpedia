-- Prove2me | solution 1 for RH1E6S06.part_012_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T17:46:01.971849+00:00
-- url     : https://prove2.me/submissions/3cd12607-80ce-41ef-ad25-1549deea6d48

import Definitions.Def_RH1E6S06_D012_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0102 : RS5.BandZeros ((26696248907 : ℝ) / 65536) ((26700959472 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0102.s0 RH1E6S06_0102.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0102.s0 RH1E6S06_0102.rest = RH1E6S06_0102.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0102.s0 :: RH1E6S06_0102.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0102.s0.t = ((26696248907 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0102.s0]
  have e1 : RH1E6S06_0102.sL.t = ((26700959472 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0102.sL]
  rw [e0, e1] at h
  exact h

theorem band_0103 : RS5.BandZeros ((26700959472 : ℝ) / 65536) ((26705688640 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0103.s0 RH1E6S06_0103.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0103.s0 RH1E6S06_0103.rest = RH1E6S06_0103.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0103.s0 :: RH1E6S06_0103.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0103.s0.t = ((26700959472 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0103.s0]
  have e1 : RH1E6S06_0103.sL.t = ((26705688640 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0103.sL]
  rw [e0, e1] at h
  exact h

theorem part_012_3 : RS5.BandZeros ((26696248907 : ℝ) / 65536) ((26705688640 : ℝ) / 65536) 254 := by
  have g0 := band_0102
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0103
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((26696248907 : ℝ) / 65536) ((26705688640 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_012_3 <;> assumption
