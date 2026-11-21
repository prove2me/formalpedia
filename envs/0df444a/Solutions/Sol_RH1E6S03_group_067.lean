-- Prove2me | solution 1 for RH1E6S03.group_067
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T07:53:46.570584+00:00
-- url     : https://prove2.me/submissions/dbfa10fc-7cb5-474f-b65c-530f3f8591bd

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S03_part_067_0
import Theorems.Thm_RH1E6S03_part_067_1
import Theorems.Thm_RH1E6S03_part_067_2
import Theorems.Thm_RH1E6S03_part_067_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem group_067 : RS5.BandZeros ((19011610526 : ℝ) / 65536) ((19050569839 : ℝ) / 65536) 1016 := by
  have g0 := part_067_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_067_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_067_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_067_3
  exact g3
end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((19011610526 : ℝ) / 65536) ((19050569839 : ℝ) / 65536) 1016 := by
  apply RH1E6S03.group_067 <;> assumption
