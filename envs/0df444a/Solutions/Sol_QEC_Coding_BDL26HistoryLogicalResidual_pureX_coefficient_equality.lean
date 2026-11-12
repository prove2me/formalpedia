-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.pureX_coefficient_equality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:36:37.852122+00:00
-- url     : https://prove2.me/submissions/5d506a26-86e3-4fa8-aa7c-2141ee039df3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Words
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_coefficient_equality
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_pureX_coefficient


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
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) :
    BDL26LogicalQubitPreservation.logicalEquiv S (n+2)
        (BDL26LogicalQubitPreservation.logicalClass S (n+2)
          (pureX S (n+2) (topCocycle S n sigma e))) =
      BDL26LogicalQubitPreservation.logicalEquiv S 2
        (BDL26LogicalQubitPreservation.logicalClass S 2
          (pureX S 2 (lowerCocycle S n sigma e u hu))) := by
  rw [pureX_coefficient,pureX_coefficient]
  exact coefficient_equality S n sigma e u hu
end QEC.Coding.BDL26HistoryLogicalResidual
