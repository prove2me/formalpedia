-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.suffixEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:44:46.124862+00:00
-- url     : https://prove2.me/submissions/0fe05108-5869-4b0f-b2ec-44a76fa4a643

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
    suffixEquiv S n a b (FC.classOf S (a.val+2) w) =
      FC.classOf S (b.val+2) (intervalCocycle S n a b hab w) :=
  (interval_facts_nat S n b.val (Nat.le_of_lt_succ b.isLt) a hab w).2
end QEC.Coding.BDL26HistoryLogicalResidual
