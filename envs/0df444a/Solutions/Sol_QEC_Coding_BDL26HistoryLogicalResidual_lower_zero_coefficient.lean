-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.lower_zero_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:39:10.614615+00:00
-- url     : https://prove2.me/submissions/1010c79d-a937-4523-943b-39fd0f2a5b22

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Words
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_coefficient_equality
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_zero_coefficient
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
    (u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) :
    lowerCoefficient S n sigma 0 u hu = 0 :=
  (coefficient_equality S n sigma 0 u hu).symm.trans (zero_coefficient S n sigma)
end QEC.Coding.BDL26HistoryLogicalResidual
