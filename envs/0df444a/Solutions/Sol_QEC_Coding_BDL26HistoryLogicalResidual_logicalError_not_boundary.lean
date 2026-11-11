-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.logicalError_not_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:46:50.146752+00:00
-- url     : https://prove2.me/submissions/ee92d2da-f6a4-49a6-96e9-80428ec01058

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Words
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_top_zero_iff_boundary
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_logicalError_coefficient

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryLogicalResidual
theorem _root_.solution (sigma : TopInput S n) :
    ¬ ∃ f : (SuffixData S n).family.Cochain0 (TopIndex n),
      (SuffixData S n).family.coboundary0 (TopIndex n) f = topWord S n sigma (logicalError S n) := by
  intro h
  have hz := (top_zero_iff_boundary S n sigma (logicalError S n)).mpr h
  rw [logicalError_coefficient] at hz
  exact one_ne_zero hz
end QEC.Coding.BDL26HistoryLogicalResidual
