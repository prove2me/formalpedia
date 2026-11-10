-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.localCx_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:49:35.755482+00:00
-- url     : https://prove2.me/submissions/7b7e7276-1548-40eb-ac20-cc7c048eb521

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Decomposition
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xDelta1_decomposition
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_reindex_delta1
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (f : Word BDL26Field (LocalRegionIndex ((localX P S).correctionRegion x))) :
    rxCoboundary1 P S (extendWordLinear ((localX P S).correctionRegion x) f) =
      extendWordLinear ((localX P S).syndromeRegion x)
        (wordLinearMapTranspose (localCx P S x).boundary2 f) +
          xFlow P S x ((wordEquiv (xCorrectionEquiv P S x)).symm f) := by
  let rawF := (wordEquiv (xCorrectionEquiv P S x)).symm f
  have he : xExtend P S x rawF = extendWordLinear ((localX P S).correctionRegion x) f := by
    change extendWordLinear _ (wordEquiv _ ((wordEquiv _).symm f)) = _
    rw [LinearEquiv.apply_symm_apply]
  have hd : wordLinearMapTranspose (localCx P S x).boundary2 f =
      wordEquiv (xSyndromeEquiv P S x)
        (wordLinearMapTranspose (doubleCylinderBoundary2 P x S) rawF) := by
    rw [localCx, reindex_delta1]
    rfl
  rw [← he, xDelta1_decomposition, hd]
  rfl
end QEC.Coding.BDL26RXDecoderAdapter
