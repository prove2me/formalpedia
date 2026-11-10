-- Prove2me | solution 1 for QEC.Coding.BDL26RXCohomology.normalized_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T02:27:06.617809+00:00
-- url     : https://prove2.me/submissions/a4127da8-eadf-4330-90c1-5743cf2a2d1a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Lifts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Representatives
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Geometry
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_word_eq_root_of_graphCoboundary_eq_zero
import Theorems.Thm_QEC_Coding_BDL26RXStagedRestriction_rxCoboundary1_q_of_x_restrictions_zero
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXCohomology
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RXDecoderAdapter BDL26ReplacementSupport
open BDL26RZMap1CoordinateBridge
open BDL26RXStagedRestriction MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXCohomology
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (w : Word Field (RX1 P S))
    (hw : rxCoboundary1 P S w = 0)
    (hx : ∀ x, restrictWordLinear ((localX P S).correctionRegion x) w = 0) :
    rxMap1Coord P S (coarseWord P S w) = w := by
  funext p
  rcases p with ⟨x,e⟩ | ⟨q,v⟩
  · have hz := congrFun (hx x) (xCorrectionEquiv P S x e)
    exact hz.symm
  · symm
    apply word_eq_root_of_graphCoboundary_eq_zero
      (qDoubleCylinderEdgeStart P q S) (qDoubleCylinderEdgeEnd P q S)
      (0, Sum.inl (Sum.inl ())) (qDoubleCylinderPath P A q S)
      (fun vertex => w (Sum.inr ⟨q,vertex⟩))
    change wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
      (fun vertex => w (Sum.inr ⟨q,vertex⟩)) = 0
    funext edge
    rw [← rxCoboundary1_q_of_x_restrictions_zero P S w hx q edge, hw]
    rfl
end QEC.Coding.BDL26RXCohomology
