-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.localCq_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:48:16.908439+00:00
-- url     : https://prove2.me/submissions/32213699-177f-4329-a0f7-73e75680a4a4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Decomposition
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qDelta1_decomposition
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_reindex_delta1
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (f : Word BDL26Field (LocalRegionIndex ((localQ P S).correctionRegion q))) :
    rxCoboundary1 P S (extendWordLinear ((localQ P S).correctionRegion q) f) =
      extendWordLinear ((localQ P S).syndromeRegion q)
        (wordLinearMapTranspose (localCq P S q).boundary2 f) +
          qFlow P S q ((wordEquiv (qCorrectionEquiv P S q)).symm f) := by
  let rawF := (wordEquiv (qCorrectionEquiv P S q)).symm f
  have he : qExtend P S q rawF = extendWordLinear ((localQ P S).correctionRegion q) f := by
    change extendWordLinear _ (wordEquiv _ ((wordEquiv _).symm f)) = _
    rw [LinearEquiv.apply_symm_apply]
  have hd : wordLinearMapTranspose (localCq P S q).boundary2 f =
      wordEquiv (qSyndromeEquiv P S q)
        (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) rawF) := by
    rw [localCq, reindex_delta1]
    rfl
  rw [← he, qDelta1_decomposition, hd]
  rfl
end QEC.Coding.BDL26RXDecoderAdapter
