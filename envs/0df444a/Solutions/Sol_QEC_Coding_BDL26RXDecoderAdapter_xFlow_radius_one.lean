-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.xFlow_radius_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:40:22.446926+00:00
-- url     : https://prove2.me/submissions/269127e0-2751-4a5d-8ec2-27196c2c1f6c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Graph
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxLevel_edge
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_distance_le_one_iff
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xFlow_at_q
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xFlow_at_x
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xFlow_at_z


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : P.X) (w : Word BDL26Field (DoubleCylinderEdge P x S))
    (p : RX2 P S) (hp : xFlow P S x w p ≠ 0) :
    DirectedGraph.distance (rxLevel P).graph (Sum.inl x) (topCenter P S p) ≤ 1 := by
  rcases p with (⟨y,f⟩ | ⟨q,e⟩) | ⟨z,c⟩
  · exact (hp (xFlow_at_x P S x y w f)).elim
  · have hxq : P.xq x q = true := by
      by_contra h
      exact hp (by rw [xFlow_at_q P A, dif_neg h])
    apply (distance_le_one_iff _ _ _).mpr
    right
    change (rxLevel P).graph.edge (Sum.inl x) (Sum.inr (Sum.inl q)) = true
    rw [rxLevel_edge, tannerLevel_edge]
    exact hxq
  · exact (hp (xFlow_at_z P S x w z c)).elim
end QEC.Coding.BDL26RXDecoderAdapter
