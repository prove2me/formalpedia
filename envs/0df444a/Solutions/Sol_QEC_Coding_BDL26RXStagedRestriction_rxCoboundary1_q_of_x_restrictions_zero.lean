-- Prove2me | solution 1 for QEC.Coding.BDL26RXStagedRestriction.rxCoboundary1_q_of_x_restrictions_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:14:17.095862+00:00
-- url     : https://prove2.me/submissions/d6cc2690-5d36-46d2-a156-751c17c2933f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXStagedRestriction
import Theorems.Thm_QEC_Coding_BDL26RXStagedRestriction_rxCoboundary1_q_of_x_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXStagedRestriction
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26ReplacementSupport BDL26ReplacementCochainMaps
open MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXStagedRestriction
theorem _root_.solution
    (P : TannerSquarePresentation) (S : OddScale) (e : Word BDL26Field (RX1 P S))
    (hX : ∀ x, restrictWordLinear (fiberRegion (rxCorrectionOwner P S) (.x x)) e = 0)
    (q : P.Q) (a : QDoubleCylinderEdge P q S) :
    rxCoboundary1 P S e (Sum.inl (Sum.inr ⟨q,a⟩)) =
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
        (fun vertex => e (Sum.inr ⟨q,vertex⟩)) a := by
  apply rxCoboundary1_q_of_x_zero P S e
  intro x edge
  exact congrFun (hX x) ⟨Sum.inl ⟨x,edge⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
end QEC.Coding.BDL26RXStagedRestriction
