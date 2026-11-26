-- Prove2me | solution 1 for Sendov.stat_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:29:28.02904+00:00
-- url     : https://prove2.me/submissions/dd644ebb-64c6-45cf-92f7-ebde83faf5c7

import Definitions.Def_Sendov_FiniteRange_Cover
import Definitions.Def_Sendov_LargeDegree_Endgame
import Definitions.Def_Sendov_Main
import Theorems.Thm_Sendov_finite_range_le_100
import Theorems.Thm_Sendov_large_degree


set_option autoImplicit false
open Sendov
variable {α : ℝ}
namespace Sendov
theorem _root_.solution {n : ℕ} (hn : 5 ≤ n) (hα : 0 ≤ α) (hα' : α ≤ 17)
    (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  rcases Nat.lt_or_ge n 101 with h | h
  · exact finite_range_le_100 hn (by omega) hα hα' hfeas
  · exact large_degree h hα hα' hfeas
end Sendov
