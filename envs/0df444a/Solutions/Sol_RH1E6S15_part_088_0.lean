-- Prove2me | solution 1 for RH1E6S15.part_088_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T13:29:52.370877+00:00
-- url     : https://prove2.me/submissions/b8842418-08eb-4044-9aa9-9e6f52d038b1

import Definitions.Def_RH1E6S15_D088_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0704 : RS5.BandZeros ((58814380003 : ℝ) / 65536) ((58818764932 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0704.s0 RH1E6S15_0704.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0704.s0 RH1E6S15_0704.rest = RH1E6S15_0704.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0704.s0 :: RH1E6S15_0704.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0704.s0.t = ((58814380003 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0704.s0]
  have e1 : RH1E6S15_0704.sL.t = ((58818764932 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0704.sL]
  rw [e0, e1] at h
  exact h

theorem band_0705 : RS5.BandZeros ((58818764932 : ℝ) / 65536) ((58823165716 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0705.s0 RH1E6S15_0705.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0705.s0 RH1E6S15_0705.rest = RH1E6S15_0705.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0705.s0 :: RH1E6S15_0705.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0705.s0.t = ((58818764932 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0705.s0]
  have e1 : RH1E6S15_0705.sL.t = ((58823165716 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0705.sL]
  rw [e0, e1] at h
  exact h

theorem part_088_0 : RS5.BandZeros ((58814380003 : ℝ) / 65536) ((58823165716 : ℝ) / 65536) 254 := by
  have g0 := band_0704
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0705
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((58814380003 : ℝ) / 65536) ((58823165716 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_088_0 <;> assumption
