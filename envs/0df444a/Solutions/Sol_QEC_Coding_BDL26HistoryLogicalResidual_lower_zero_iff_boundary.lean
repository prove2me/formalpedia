-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.lower_zero_iff_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:02:44.217117+00:00
-- url     : https://prove2.me/submissions/f0aa552c-7fd8-40ad-acc5-169aa3ba16d4

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
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) :
    lowerCoefficient S n sigma e u hu = 0 ↔
      ∃ f : (SuffixData S n).family.Cochain0 0,
        (SuffixData S n).family.coboundary0 0 f = lowerWord S n sigma e u := by
  have h := coefficient_zero_iff_boundary S 2 (lowerCocycle S n sigma e u hu)
  have hd : (SuffixData S n).family.coboundary0 0 =
      tannerCoboundary0 (state S 2).presentation := suffix_delta0 S n (0 : LevelIndex n)
  rw [← hd] at h
  exact h
end QEC.Coding.BDL26HistoryLogicalResidual
