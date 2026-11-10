-- Prove2me | solution 1 for QEC.Coding.BDL26GraphQuantitativeBounds.rxSyndromeCellToFiber_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:49:54.310228+00:00
-- url     : https://prove2.me/submissions/092bf364-3e9e-48df-8d15-ac75c65e65ae

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GraphQuantitativeBounds
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26RXLocalReplacement
open scoped BigOperators Classical
open BDL26ReplacementSupport
namespace QEC.Coding.BDL26GraphQuantitativeBounds
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (u : Vertex P) : Function.Surjective (rxSyndromeCellToFiber P S u) := by
  rintro ⟨c,hc⟩
  rcases c with (⟨x,a⟩ | ⟨q,a⟩) | ⟨z,a⟩
  · change Vertex.x x = u at hc
    subst u
    exact ⟨a,rfl⟩
  · change Vertex.q q = u at hc
    subst u
    exact ⟨a,rfl⟩
  · change Vertex.z z = u at hc
    subst u
    exact ⟨a,rfl⟩
end QEC.Coding.BDL26GraphQuantitativeBounds
