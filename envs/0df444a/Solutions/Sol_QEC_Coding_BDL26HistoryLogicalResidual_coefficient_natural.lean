-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.coefficient_natural
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:04:51.61968+00:00
-- url     : https://prove2.me/submissions/6e10f2b2-611c-45c7-a71b-6056ca418d11

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Intervals
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
theorem _root_.solution (a b : LevelIndex n) (x : FC.H1 S (a.val+2)) :
    FC.finiteH1Equiv S (b.val+2) (suffixEquiv S n a b x) =
      FC.finiteH1Equiv S (a.val+2) x := by
  change BDL26SeedCohomology.stateZeroEquivalence S
    ((FC.prefixEquiv S (b.val+2)).symm
      (FC.prefixEquiv S (b.val+2) ((FC.prefixEquiv S (a.val+2)).symm x))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl
end QEC.Coding.BDL26HistoryLogicalResidual
