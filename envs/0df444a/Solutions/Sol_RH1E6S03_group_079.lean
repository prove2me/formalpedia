-- Prove2me | solution 1 for RH1E6S03.group_079
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T08:21:02.379168+00:00
-- url     : https://prove2.me/submissions/da68e156-5b99-448a-9ed6-4a91e5fd6e39

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S03_part_079_0
import Theorems.Thm_RH1E6S03_part_079_1
import Theorems.Thm_RH1E6S03_part_079_2
import Theorems.Thm_RH1E6S03_part_079_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem group_079 : RS5.BandZeros ((19478522305 : ℝ) / 65536) ((19517393910 : ℝ) / 65536) 1016 := by
  have g0 := part_079_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_079_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_079_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_079_3
  exact g3
end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((19478522305 : ℝ) / 65536) ((19517393910 : ℝ) / 65536) 1016 := by
  apply RH1E6S03.group_079 <;> assumption
