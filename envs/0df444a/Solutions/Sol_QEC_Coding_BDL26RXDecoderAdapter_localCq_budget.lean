-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.localCq_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:46:11.304437+00:00
-- url     : https://prove2.me/submissions/763a286a-bc47-4e86-81ac-064104383c5d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Budgets
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCq_delta1_apply
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qFlow_weight
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_wordEquiv_weight
import Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_rxCq_exists_global_outgoing_weight_le
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (s : Word BDL26Field (LocalRegionIndex ((localQ P S).syndromeRegion q)))
    (hs : s ∈ LinearMap.range (wordLinearMapTranspose (localCq P S q).boundary2)) :
    ∃ f : Word BDL26Field (LocalRegionIndex ((localQ P S).correctionRegion q)),
      wordLinearMapTranspose (localCq P S q).boundary2 f = s ∧
        HammingWeight (qFlow P S q ((wordEquiv (qCorrectionEquiv P S q)).symm f)) ≤
          HammingWeight s := by
  let rawS := (wordEquiv (qSyndromeEquiv P S q)).symm s
  have hrange : rawS ∈ LinearMap.range (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)) := by
    obtain ⟨f,hf⟩ := hs
    refine ⟨(wordEquiv (qCorrectionEquiv P S q)).symm f, ?_⟩
    funext edge
    have h := congrFun hf (qSyndromeEquiv P S q edge)
    rw [localCq_delta1_apply] at h
    exact h
  obtain ⟨rawF,hf,hw⟩ := rxCq_exists_global_outgoing_weight_le P q S rawS hrange
  refine ⟨wordEquiv (qCorrectionEquiv P S q) rawF, ?_, ?_⟩
  · funext p
    obtain ⟨edge,rfl⟩ := (qSyndromeEquiv P S q).surjective p
    rw [localCq_delta1_apply, LinearEquiv.symm_apply_apply, hf]
    rfl
  · rw [LinearEquiv.symm_apply_apply, qFlow_weight]
    have hweight : HammingWeight rawS = HammingWeight s :=
      wordEquiv_weight (qSyndromeEquiv P S q).symm s
    exact hw.trans_eq hweight
end QEC.Coding.BDL26RXDecoderAdapter
