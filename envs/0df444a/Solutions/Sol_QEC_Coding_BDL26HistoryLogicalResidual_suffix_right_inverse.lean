-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.suffix_right_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:35:47.137203+00:00
-- url     : https://prove2.me/submissions/0b5e1567-72e3-468a-bbd3-596e5d0d9127

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
theorem _root_.solution (a b : LevelIndex n) (x : FC.H1 S (b.val+2)) :
    suffixEquiv S n a b ((suffixEquiv S n a b).symm x) = x :=
  (suffixEquiv S n a b).apply_symm_apply x
end QEC.Coding.BDL26HistoryLogicalResidual
