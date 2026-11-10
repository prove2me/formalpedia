-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.xLocalDelta1_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:39:08.561828+00:00
-- url     : https://prove2.me/submissions/417f4c6f-5eb5-4e88-9588-9cc2aa6a6379

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Decomposition
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xSyndromeExtend_same
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xSyndromeExtend_outside
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localDelta1_at_z
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xExtend_at_q
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xExtend_at_x
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xExtend_other
import Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_rxLocalDelta1_apply_q
import Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_rxLocalDelta1_apply_x
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (w : Word BDL26Field (DoubleCylinderEdge P x S)) :
    rxLocalDelta1 P S (xExtend P S x w) =
      xSyndromeExtend P S x (wordLinearMapTranspose (doubleCylinderBoundary2 P x S) w) := by
  funext p
  rcases p with (⟨y,f⟩ | ⟨q,e⟩) | ⟨z,c⟩
  · rw [rxLocalDelta1_apply_x]
    by_cases h : y = x
    · subst y
      have hw : (fun e => xExtend P S x w (Sum.inl ⟨x,e⟩)) = w := by
        funext e; exact xExtend_at_x P S x w e
      rw [hw, xSyndromeExtend_same]
    · have hw : (fun e => xExtend P S x w (Sum.inl ⟨y,e⟩)) = 0 := by
        funext e; exact xExtend_other P S x y h w e
      rw [hw, map_zero]
      exact (xSyndromeExtend_outside P S x _ (Sum.inl (Sum.inl ⟨y,f⟩)) (fun hh => h (Vertex.x.inj hh))).symm
  · rw [rxLocalDelta1_apply_q]
    have hw : (fun v => xExtend P S x w (Sum.inr ⟨q,v⟩)) = 0 := by
      funext v; exact xExtend_at_q P S x w q v
    rw [hw, map_zero]
    exact (xSyndromeExtend_outside P S x _ _ (by intro hh; cases hh)).symm
  · rw [localDelta1_at_z]
    exact (xSyndromeExtend_outside P S x _ _ (by intro hh; cases hh)).symm
end QEC.Coding.BDL26RXDecoderAdapter
