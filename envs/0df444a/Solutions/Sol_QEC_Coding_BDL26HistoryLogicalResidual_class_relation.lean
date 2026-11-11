-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.class_relation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:57:22.922099+00:00
-- url     : https://prove2.me/submissions/070678a6-2e19-4e85-a229-67ddeb4f641b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Words
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_class_eq_iff_boundary
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_full_identity
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_intervalCocycle_word
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffixEquiv_mk
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta0
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
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) :
    FC.classOf S (n+2) (topCocycle S n sigma e) =
      suffixEquiv S n 0 (TopIndex n) (FC.classOf S 2 (lowerCocycle S n sigma e u hu)) := by
  let v := intervalCocycle S n 0 (TopIndex n) (Nat.zero_le _)
    (lowerCocycle S n sigma e u hu)
  have hboundary : FC.classOf S (n+2) (topCocycle S n sigma e) =
      FC.classOf S (n+2) v := by
    apply (class_eq_iff_boundary S (n+2) _ _).mpr
    refine ⟨residualPotential S n e u, ?_⟩
    have hi := full_identity S n sigma e u hu
    have hv := intervalCocycle_word S n 0 (TopIndex n) (Nat.zero_le _)
      (lowerCocycle S n sigma e u hu)
    change v.val = intervalMap1 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
      (lowerWord S n sigma e u) at hv
    change tannerCoboundary0 (state S (n+2)).presentation (residualPotential S n e u) =
      topWord S n sigma e - v.val
    rw [← suffix_delta0 S n (TopIndex n),hv,hi]
    abel
  exact hboundary.trans (suffixEquiv_mk S n 0 (TopIndex n) (Nat.zero_le _)
    (lowerCocycle S n sigma e u hu)).symm
end QEC.Coding.BDL26HistoryLogicalResidual
