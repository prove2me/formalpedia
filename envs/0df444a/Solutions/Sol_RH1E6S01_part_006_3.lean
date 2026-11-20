-- Prove2me | solution 1 for RH1E6S01.part_006_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T23:34:59.995949+00:00
-- url     : https://prove2.me/submissions/87392687-7d05-4711-8522-eed999d0fd62

import Definitions.Def_RH1E6S01_D006_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0054 : RS5.BandZeros ((10110131534 : ℝ) / 65536) ((10115314958 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0054.s0 RH1E6S01_0054.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0054.s0 RH1E6S01_0054.rest = RH1E6S01_0054.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0054.s0 :: RH1E6S01_0054.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0054.s0.t = ((10110131534 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0054.s0]
  have e1 : RH1E6S01_0054.sL.t = ((10115314958 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0054.sL]
  rw [e0, e1] at h
  exact h

theorem band_0055 : RS5.BandZeros ((10115314958 : ℝ) / 65536) ((10120487937 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0055.s0 RH1E6S01_0055.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0055.s0 RH1E6S01_0055.rest = RH1E6S01_0055.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0055.s0 :: RH1E6S01_0055.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0055.s0.t = ((10115314958 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0055.s0]
  have e1 : RH1E6S01_0055.sL.t = ((10120487937 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0055.sL]
  rw [e0, e1] at h
  exact h

theorem part_006_3 : RS5.BandZeros ((10110131534 : ℝ) / 65536) ((10120487937 : ℝ) / 65536) 254 := by
  have g0 := band_0054
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0055
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((10110131534 : ℝ) / 65536) ((10120487937 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_006_3 <;> assumption
