-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.representative_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:38:46.306821+00:00
-- url     : https://prove2.me/submissions/af17d932-6a94-47d4-a623-72af785e8f17

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Words
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_representative_independent
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_coefficient_eq_iff_boundary
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
    (e u v : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val)
    (hv : (SuffixData S n).family.coboundary1 (TopIndex n) v = sigma.val) :
    ∃ f2 : (SuffixData S n).family.Cochain0 0,
      (SuffixData S n).family.coboundary0 0 f2 = lowerWord S n sigma e u-lowerWord S n sigma e v := by
  have h := (coefficient_eq_iff_boundary S 2 (lowerCocycle S n sigma e u hu)
    (lowerCocycle S n sigma e v hv)).mp (representative_independent S n sigma e u v hu hv)
  have hd : (SuffixData S n).family.coboundary0 0 =
      tannerCoboundary0 (state S 2).presentation := suffix_delta0 S n (0 : LevelIndex n)
  rw [← hd] at h
  exact h
end QEC.Coding.BDL26HistoryLogicalResidual
