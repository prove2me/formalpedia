-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.suffixEquiv_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:34:55.972289+00:00
-- url     : https://prove2.me/submissions/0fddcbf5-a7b0-49df-ae7b-21e54b5e00bb

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
theorem _root_.solution (a b c : LevelIndex n) (x : FC.H1 S (a.val+2)) :
    suffixEquiv S n b c (suffixEquiv S n a b x) = suffixEquiv S n a c x := by
  change FC.prefixEquiv S (c.val+2)
    ((FC.prefixEquiv S (b.val+2)).symm
      (FC.prefixEquiv S (b.val+2) ((FC.prefixEquiv S (a.val+2)).symm x))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl
end QEC.Coding.BDL26HistoryLogicalResidual
