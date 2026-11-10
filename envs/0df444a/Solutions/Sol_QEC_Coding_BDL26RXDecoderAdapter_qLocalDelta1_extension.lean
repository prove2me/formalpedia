-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.qLocalDelta1_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:39:14.266508+00:00
-- url     : https://prove2.me/submissions/30142921-579c-4ba3-940e-0eb9325e15a7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Decomposition
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qSyndromeExtend_same
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qSyndromeExtend_outside
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localDelta1_at_z
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qExtend_at_q
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qExtend_at_x
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qExtend_other
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
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) :
    rxLocalDelta1 P S (qExtend P S q w) =
      qSyndromeExtend P S q (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) w) := by
  funext p
  rcases p with (⟨x,f⟩ | ⟨r,e⟩) | ⟨z,c⟩
  · rw [rxLocalDelta1_apply_x]
    have hw : (fun e => qExtend P S q w (Sum.inl ⟨x,e⟩)) = 0 := by
      funext e; exact qExtend_at_x P S q w x e
    rw [hw, map_zero]
    exact (qSyndromeExtend_outside P S q _ _ (by intro hh; cases hh)).symm
  · rw [rxLocalDelta1_apply_q]
    by_cases h : r = q
    · subst r
      have hw : (fun v => qExtend P S q w (Sum.inr ⟨q,v⟩)) = w := by
        funext v; exact qExtend_at_q P S q w v
      rw [hw, qSyndromeExtend_same]
    · have hw : (fun v => qExtend P S q w (Sum.inr ⟨r,v⟩)) = 0 := by
        funext v; exact qExtend_other P S q r h w v
      rw [hw, map_zero]
      exact (qSyndromeExtend_outside P S q _ (Sum.inl (Sum.inr ⟨r,e⟩)) (fun hh => h (Vertex.q.inj hh))).symm
  · rw [localDelta1_at_z]
    exact (qSyndromeExtend_outside P S q _ _ (by intro hh; cases hh)).symm
end QEC.Coding.BDL26RXDecoderAdapter
