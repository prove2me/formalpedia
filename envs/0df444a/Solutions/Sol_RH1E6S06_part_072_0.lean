-- Prove2me | solution 1 for RH1E6S06.part_072_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T21:57:18.153865+00:00
-- url     : https://prove2.me/submissions/3502d273-e66c-4141-a4d6-7e29600d193b

import Definitions.Def_RH1E6S06_D072_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0576 : RS5.BandZeros ((28925334404 : ℝ) / 65536) ((28930036894 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0576.s0 RH1E6S06_0576.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0576.s0 RH1E6S06_0576.rest = RH1E6S06_0576.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0576.s0 :: RH1E6S06_0576.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0576.s0.t = ((28925334404 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0576.s0]
  have e1 : RH1E6S06_0576.sL.t = ((28930036894 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0576.sL]
  rw [e0, e1] at h
  exact h

theorem band_0577 : RS5.BandZeros ((28930036894 : ℝ) / 65536) ((28934712024 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0577.s0 RH1E6S06_0577.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0577.s0 RH1E6S06_0577.rest = RH1E6S06_0577.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0577.s0 :: RH1E6S06_0577.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0577.s0.t = ((28930036894 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0577.s0]
  have e1 : RH1E6S06_0577.sL.t = ((28934712024 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0577.sL]
  rw [e0, e1] at h
  exact h

theorem part_072_0 : RS5.BandZeros ((28925334404 : ℝ) / 65536) ((28934712024 : ℝ) / 65536) 254 := by
  have g0 := band_0576
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0577
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((28925334404 : ℝ) / 65536) ((28934712024 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_072_0 <;> assumption
