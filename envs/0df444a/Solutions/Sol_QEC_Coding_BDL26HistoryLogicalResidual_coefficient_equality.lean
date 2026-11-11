-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.coefficient_equality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:04:50.130367+00:00
-- url     : https://prove2.me/submissions/d6279cca-7935-493d-b67c-444bbd383e56

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Words
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_class_relation
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_coefficient_natural


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
    topCoefficient S n sigma e = lowerCoefficient S n sigma e u hu := by
  unfold topCoefficient lowerCoefficient
  rw [class_relation S n sigma e u hu]
  exact coefficient_natural S n 0 (TopIndex n) _
end QEC.Coding.BDL26HistoryLogicalResidual
