-- Prove2me | solution 1 for RH1E6S12.part_063_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T10:28:49.185959+00:00
-- url     : https://prove2.me/submissions/2c0c8f56-77fb-4e06-911d-6670f87f9a45

import Definitions.Def_RH1E6S12_D063_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0508 : RS5.BandZeros ((48156471805 : ℝ) / 65536) ((48160953166 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0508.s0 RH1E6S12_0508.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0508.s0 RH1E6S12_0508.rest = RH1E6S12_0508.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0508.s0 :: RH1E6S12_0508.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0508.s0.t = ((48156471805 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0508.s0]
  have e1 : RH1E6S12_0508.sL.t = ((48160953166 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0508.sL]
  rw [e0, e1] at h
  exact h

theorem band_0509 : RS5.BandZeros ((48160953166 : ℝ) / 65536) ((48165416848 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0509.s0 RH1E6S12_0509.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0509.s0 RH1E6S12_0509.rest = RH1E6S12_0509.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0509.s0 :: RH1E6S12_0509.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0509.s0.t = ((48160953166 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0509.s0]
  have e1 : RH1E6S12_0509.sL.t = ((48165416848 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0509.sL]
  rw [e0, e1] at h
  exact h

theorem part_063_2 : RS5.BandZeros ((48156471805 : ℝ) / 65536) ((48165416848 : ℝ) / 65536) 254 := by
  have g0 := band_0508
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0509
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((48156471805 : ℝ) / 65536) ((48165416848 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_063_2 <;> assumption
