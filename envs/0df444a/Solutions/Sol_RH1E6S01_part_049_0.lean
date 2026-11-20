-- Prove2me | solution 1 for RH1E6S01.part_049_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T01:02:19.757259+00:00
-- url     : https://prove2.me/submissions/deba41e8-1110-4ce0-9bfd-f20a49ed794b

import Definitions.Def_RH1E6S01_D049_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0392 : RS5.BandZeros ((11844786277 : ℝ) / 65536) ((11849889779 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0392.s0 RH1E6S01_0392.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0392.s0 RH1E6S01_0392.rest = RH1E6S01_0392.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0392.s0 :: RH1E6S01_0392.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0392.s0.t = ((11844786277 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0392.s0]
  have e1 : RH1E6S01_0392.sL.t = ((11849889779 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0392.sL]
  rw [e0, e1] at h
  exact h

theorem band_0393 : RS5.BandZeros ((11849889779 : ℝ) / 65536) ((11854973014 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0393.s0 RH1E6S01_0393.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0393.s0 RH1E6S01_0393.rest = RH1E6S01_0393.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0393.s0 :: RH1E6S01_0393.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0393.s0.t = ((11849889779 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0393.s0]
  have e1 : RH1E6S01_0393.sL.t = ((11854973014 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0393.sL]
  rw [e0, e1] at h
  exact h

theorem part_049_0 : RS5.BandZeros ((11844786277 : ℝ) / 65536) ((11854973014 : ℝ) / 65536) 254 := by
  have g0 := band_0392
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0393
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((11844786277 : ℝ) / 65536) ((11854973014 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_049_0 <;> assumption
