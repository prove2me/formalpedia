-- Prove2me | solution 1 for RH1E6S03.part_051_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T07:09:38.47136+00:00
-- url     : https://prove2.me/submissions/01c8966f-08c5-4a77-b264-18acf91e1382

import Definitions.Def_RH1E6S03_D051_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0412 : RS5.BandZeros ((18406936779 : ℝ) / 65536) ((18411810983 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0412.s0 RH1E6S03_0412.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0412.s0 RH1E6S03_0412.rest = RH1E6S03_0412.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0412.s0 :: RH1E6S03_0412.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0412.s0.t = ((18406936779 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0412.s0]
  have e1 : RH1E6S03_0412.sL.t = ((18411810983 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0412.sL]
  rw [e0, e1] at h
  exact h

theorem band_0413 : RS5.BandZeros ((18411810983 : ℝ) / 65536) ((18416713907 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0413.s0 RH1E6S03_0413.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0413.s0 RH1E6S03_0413.rest = RH1E6S03_0413.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0413.s0 :: RH1E6S03_0413.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0413.s0.t = ((18411810983 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0413.s0]
  have e1 : RH1E6S03_0413.sL.t = ((18416713907 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0413.sL]
  rw [e0, e1] at h
  exact h

theorem part_051_2 : RS5.BandZeros ((18406936779 : ℝ) / 65536) ((18416713907 : ℝ) / 65536) 254 := by
  have g0 := band_0412
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0413
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((18406936779 : ℝ) / 65536) ((18416713907 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_051_2 <;> assumption
