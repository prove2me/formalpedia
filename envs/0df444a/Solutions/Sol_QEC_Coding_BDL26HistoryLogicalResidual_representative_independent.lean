-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.representative_independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:39:34.701192+00:00
-- url     : https://prove2.me/submissions/ab19ef95-cd2d-4944-969c-f8edb3bf09ba

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Words
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_coefficient_equality
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
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
theorem _root_.solution (sigma : TopInput S n)
    (e u v : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val)
    (hv : (SuffixData S n).family.coboundary1 (TopIndex n) v = sigma.val) :
    lowerCoefficient S n sigma e u hu = lowerCoefficient S n sigma e v hv :=
  (coefficient_equality S n sigma e u hu).symm.trans (coefficient_equality S n sigma e v hv)
end QEC.Coding.BDL26HistoryLogicalResidual
