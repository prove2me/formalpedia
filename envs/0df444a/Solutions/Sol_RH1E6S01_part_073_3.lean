-- Prove2me | solution 1 for RH1E6S01.part_073_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T01:53:52.238123+00:00
-- url     : https://prove2.me/submissions/286ef193-9ce3-4116-9ae3-5427491b39da

import Definitions.Def_RH1E6S01_D073_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0590 : RS5.BandZeros ((12849289377 : ℝ) / 65536) ((12854342796 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0590.s0 RH1E6S01_0590.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0590.s0 RH1E6S01_0590.rest = RH1E6S01_0590.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0590.s0 :: RH1E6S01_0590.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0590.s0.t = ((12849289377 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0590.s0]
  have e1 : RH1E6S01_0590.sL.t = ((12854342796 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0590.sL]
  rw [e0, e1] at h
  exact h

theorem band_0591 : RS5.BandZeros ((12854342796 : ℝ) / 65536) ((12859396023 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0591.s0 RH1E6S01_0591.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0591.s0 RH1E6S01_0591.rest = RH1E6S01_0591.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0591.s0 :: RH1E6S01_0591.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0591.s0.t = ((12854342796 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0591.s0]
  have e1 : RH1E6S01_0591.sL.t = ((12859396023 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0591.sL]
  rw [e0, e1] at h
  exact h

theorem part_073_3 : RS5.BandZeros ((12849289377 : ℝ) / 65536) ((12859396023 : ℝ) / 65536) 254 := by
  have g0 := band_0590
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0591
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((12849289377 : ℝ) / 65536) ((12859396023 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_073_3 <;> assumption
