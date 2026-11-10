-- Prove2me | solution 1 for QEC.Coding.BDL26RXLocalReplacement.qLocalCoboundary_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:13:59.761875+00:00
-- url     : https://prove2.me/submissions/a30d2b3c-c4ac-4d49-a7ba-7efba7e1f1bb

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QLocalWeight

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open scoped BigOperators
namespace QEC.Coding.BDL26RXLocalReplacement
theorem _root_.solution (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (f : Word Field (QDoubleCylinderVertex P q S))
    (edge : QDoubleCylinderEdge P q S) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) f edge =
      f (qDoubleCylinderEdgeStart P q S edge) +
        f (qDoubleCylinderEdgeEnd P q S edge) := by
  unfold qDoubleCylinderBoundary1
  exact wordLinearMapTranspose_graphBoundary_apply _ _ _ _
end QEC.Coding.BDL26RXLocalReplacement
