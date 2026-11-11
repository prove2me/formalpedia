-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.boundary_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:33:23.403781+00:00
-- url     : https://prove2.me/submissions/b3d53a37-7a88-496b-a924-efcc710249b8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Words
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_coefficient_equality
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_top_zero_iff_boundary
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_lower_zero_iff_boundary

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
    (∃ f : (SuffixData S n).family.Cochain0 (TopIndex n),
      (SuffixData S n).family.coboundary0 (TopIndex n) f = topWord S n sigma e) ↔
      ∃ f : (SuffixData S n).family.Cochain0 0,
        (SuffixData S n).family.coboundary0 0 f = lowerWord S n sigma e u := by
  rw [← top_zero_iff_boundary,← lower_zero_iff_boundary,coefficient_equality S n sigma e u hu]
end QEC.Coding.BDL26HistoryLogicalResidual
