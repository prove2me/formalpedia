-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.top_zero_iff_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:45:50.792499+00:00
-- url     : https://prove2.me/submissions/fb5a71cd-9620-42b4-abd4-ea73ffceb047

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Words
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_coefficient_zero_iff_boundary
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta0


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
    (e : (SuffixData S n).family.Cochain1 (TopIndex n)) :
    topCoefficient S n sigma e = 0 ↔
      ∃ f : (SuffixData S n).family.Cochain0 (TopIndex n),
        (SuffixData S n).family.coboundary0 (TopIndex n) f = topWord S n sigma e := by
  have h := coefficient_zero_iff_boundary S (n+2) (topCocycle S n sigma e)
  rw [← suffix_delta0 S n (TopIndex n)] at h
  exact h
end QEC.Coding.BDL26HistoryLogicalResidual
