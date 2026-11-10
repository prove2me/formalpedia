-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.localCx_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:46:08.602887+00:00
-- url     : https://prove2.me/submissions/a7ba1f7b-aedb-40fe-b748-45eeb3734ab3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Budgets
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCx_delta1_apply
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_wordEquiv_weight
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xFlow_weight
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCx_exists_local_weight_le_all_q
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (x : P.X)
    (s : Word BDL26Field (LocalRegionIndex ((localX P S).syndromeRegion x)))
    (hs : s ∈ LinearMap.range (wordLinearMapTranspose (localCx P S x).boundary2)) :
    ∃ f : Word BDL26Field (LocalRegionIndex ((localX P S).correctionRegion x)),
      wordLinearMapTranspose (localCx P S x).boundary2 f = s ∧
        HammingWeight (xFlow P S x ((wordEquiv (xCorrectionEquiv P S x)).symm f)) ≤
          HammingWeight s := by
  let rawS := (wordEquiv (xSyndromeEquiv P S x)).symm s
  have hrange : rawS ∈ LinearMap.range (wordLinearMapTranspose (doubleCylinderBoundary2 P x S)) := by
    obtain ⟨f,hf⟩ := hs
    refine ⟨(wordEquiv (xCorrectionEquiv P S x)).symm f, ?_⟩
    funext face
    have h := congrFun hf (xSyndromeEquiv P S x face)
    rw [localCx_delta1_apply] at h
    exact h
  obtain ⟨rawF,hf,hw⟩ := rxCx_exists_local_weight_le_all_q
    P A R x S rawS hrange
  refine ⟨wordEquiv (xCorrectionEquiv P S x) rawF, ?_, ?_⟩
  · funext p
    obtain ⟨face,rfl⟩ := (xSyndromeEquiv P S x).surjective p
    rw [localCx_delta1_apply, LinearEquiv.symm_apply_apply, hf]
    rfl
  · rw [LinearEquiv.symm_apply_apply, xFlow_weight P A.toTannerSquareAdmissibleV2.toTannerSquareAdmissible]
    have hweight : HammingWeight rawS = HammingWeight s :=
      wordEquiv_weight (xSyndromeEquiv P S x).symm s
    exact hw.trans_eq hweight
end QEC.Coding.BDL26RXDecoderAdapter
