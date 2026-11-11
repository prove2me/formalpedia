-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.suffixEquiv_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:23:21.179205+00:00
-- url     : https://prove2.me/submissions/f57ad77c-def5-45d7-8413-63ad0d0292df

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Intervals
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_prefixEquiv_succ
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryLogicalResidual
theorem _root_.solution (a : LevelIndex n) (i : StepIndex n)
    (x : FC.H1 S (a.val+2)) :
    suffixEquiv S n a i.succ x =
      FC.stepEquiv S (i.val+2) (suffixEquiv S n a i.castSucc x) := by
  change FC.prefixEquiv S ((i.val+2)+1) ((FC.prefixEquiv S (a.val+2)).symm x) = _
  rw [FC.prefixEquiv_succ]
  rfl
end QEC.Coding.BDL26HistoryLogicalResidual
