-- Prove2me | solution 1 for RH1E6S00.part_008_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T21:07:08.549975+00:00
-- url     : https://prove2.me/submissions/4584a28f-1e65-4175-ad87-ea7f486d8e2d

import Definitions.Def_RH1E6S00_D008_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0070 : RS5.BandZeros ((6930858917 : ℝ) / 65536) ((6936232797 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0070.s0 RH1E6S00_0070.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0070.s0 RH1E6S00_0070.rest = RH1E6S00_0070.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0070.s0 :: RH1E6S00_0070.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0070.s0.t = ((6930858917 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0070.s0]
  have e1 : RH1E6S00_0070.sL.t = ((6936232797 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0070.sL]
  rw [e0, e1] at h
  exact h

theorem band_0071 : RS5.BandZeros ((6936232797 : ℝ) / 65536) ((6941627404 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0071.s0 RH1E6S00_0071.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0071.s0 RH1E6S00_0071.rest = RH1E6S00_0071.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0071.s0 :: RH1E6S00_0071.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0071.s0.t = ((6936232797 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0071.s0]
  have e1 : RH1E6S00_0071.sL.t = ((6941627404 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0071.sL]
  rw [e0, e1] at h
  exact h

theorem part_008_3 : RS5.BandZeros ((6930858917 : ℝ) / 65536) ((6941627404 : ℝ) / 65536) 254 := by
  have g0 := band_0070
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0071
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((6930858917 : ℝ) / 65536) ((6941627404 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_008_3 <;> assumption
