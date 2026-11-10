-- Prove2me | solution 1 for QEC.Coding.BDL26RXLocalReplacement.rxCxH0Coordinate_bijective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:12:52.89469+00:00
-- url     : https://prove2.me/submissions/83f658d6-e669-4789-9e70-3a41a1695171

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCxCocycle_eq_boundaryRoot_zeroCopy

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity
universe u
namespace QEC.Coding.BDL26RXLocalReplacement
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (x : P.X) (S : OddScale) :
    Function.Bijective (rxCxH0Coordinate P A x S) := by
  classical
  constructor
  · intro first second hcoordinate
    apply Subtype.ext
    funext vertex
    rw [rxCxCocycle_eq_boundaryRoot_zeroCopy P A x S first.1 first.2 vertex,
      rxCxCocycle_eq_boundaryRoot_zeroCopy P A x S second.1 second.2 vertex]
    exact hcoordinate
  · intro value
    let constant : Word Field (DoubleCylinderVertex P x S) := fun _ => value
    have hgraph : wordLinearMapTranspose
        (graphBoundary (tannerDoubleCylinderEdgeStart P x S)
          (tannerDoubleCylinderEdgeEnd P x S)) constant = 0 := by
      ext edge
      rw [wordLinearMapTranspose_graphBoundary_apply]
      change value + value = 0
      exact ZModModule.add_self value
    have hkernel :
        wordLinearMapTranspose (rxCx P x S).boundary1 constant = 0 := by
      change wordLinearMapTranspose (doubleCylinderBoundary1 P x S) constant = 0
      rw [← doubleCylinderGraphBoundary_eq_boundary1]
      exact hgraph
    exact ⟨⟨constant, hkernel⟩, rfl⟩
end QEC.Coding.BDL26RXLocalReplacement
