-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.intervalCocycle_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:43:02.003987+00:00
-- url     : https://prove2.me/submissions/4f7278aa-c40a-4a39-a716-3518c6ffae61

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Intervals
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_interval_facts_nat

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryLogicalResidual
theorem _root_.solution (a b : LevelIndex n) (hab : a.val ≤ b.val)
    (w : FC.Cocycle S (a.val+2)) :
    (intervalCocycle S n a b hab w).val = intervalMap1 (SuffixData S n) a b hab w.val :=
  (interval_facts_nat S n b.val (Nat.le_of_lt_succ b.isLt) a hab w).1
end QEC.Coding.BDL26HistoryLogicalResidual
