-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.qFlow_radius_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:40:36.862552+00:00
-- url     : https://prove2.me/submissions/b96be5a2-5c0e-47fc-bbdd-e384c660a689

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Graph
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxLevel_edge
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_distance_le_one_iff
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qFlow_at_q
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qFlow_at_x
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qFlow_at_z
import Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_rxQOutgoing_nonincident
attribute [local simp] QEC.Coding.BDL26ReplacementSupport.rxQOutgoing_nonincident



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S))
    (p : RX2 P S) (hp : qFlow P S q w p ≠ 0) :
    DirectedGraph.distance (rxLevel P).graph (Sum.inr (Sum.inl q)) (topCenter P S p) ≤ 1 := by
  rcases p with (⟨x,f⟩ | ⟨r,e⟩) | ⟨z,c⟩
  · exact (hp (qFlow_at_x P S q w x f)).elim
  · exact (hp (qFlow_at_q P S q r w e)).elim
  · have hqz : P.qz q z = true := by
      by_contra h
      exact hp (by rw [qFlow_at_z, rxQOutgoing_nonincident P q S w z h]; rfl)
    apply (distance_le_one_iff _ _ _).mpr
    right
    change (rxLevel P).graph.edge (Sum.inr (Sum.inl q)) (Sum.inr (Sum.inr z)) = true
    rw [rxLevel_edge, tannerLevel_edge]
    exact hqz
end QEC.Coding.BDL26RXDecoderAdapter
