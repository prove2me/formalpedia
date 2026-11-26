-- Prove2me | solution 1 for Sendov.stat_contradiction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:30:26.402258+00:00
-- url     : https://prove2.me/submissions/7a02e3f8-87d7-4c21-a4df-6b5edcc399e2

import Definitions.Def_Sendov_FiniteRange_Cover
import Definitions.Def_Sendov_LargeDegree_Endgame
import Definitions.Def_Sendov_Main
import Theorems.Thm_Sendov_stat_lt_one

set_option autoImplicit false
open Sendov
variable {α : ℝ}
namespace Sendov
theorem _root_.solution {n : ℕ} (hn : 5 ≤ n) (hα : 0 ≤ α) (hα' : α ≤ 17)
    (hfeas : c n α ^ 2 ≤ A n α) (hstat : 1 ≤ R n α) : False :=
  absurd hstat (not_le.2 (stat_lt_one hn hα hα' hfeas))
end Sendov
