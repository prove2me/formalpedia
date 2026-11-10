-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementCochainMaps.constant_doubleCylinder_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:06:28.487515+00:00
-- url     : https://prove2.me/submissions/d03173a2-871a-43b3-b96a-e7f76e2b2b02

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementCochainMaps
open scoped BigOperators Classical
open QEC.Coding
open QEC.Coding.BDL26FiniteTannerSquare
open QEC.Coding.BDL26TannerLocalRegularity
open QEC.Coding.BDL26RXLocalReplacement
open QEC.Coding.BDL26RZLocalReplacement
open QEC.Coding.BDL26RZMap1CoordinateBridge
open QEC.Coding.MultiscaleDecoder
namespace QEC.Coding.BDL26ReplacementCochainMaps
theorem _root_.solution
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) :
    wordLinearMapTranspose (doubleCylinderBoundary1 P x S)
        (fun _ => (1 : Field)) = 0 := by
  classical
  rw [← doubleCylinderGraphBoundary_eq_boundary1]
  change wordLinearMapTranspose
      (graphBoundary (tannerDoubleCylinderEdgeStart P x S)
        (tannerDoubleCylinderEdgeEnd P x S)) (fun _ => (1 : Field)) = 0
  ext edge
  rw [wordLinearMapTranspose_graphBoundary_apply]
  exact ZModModule.add_self 1
end QEC.Coding.BDL26ReplacementCochainMaps
