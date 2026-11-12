-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementCochainMaps.constant_qDoubleCylinder_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:01:02.719858+00:00
-- url     : https://prove2.me/submissions/ee2d0ca7-bffc-4998-ab10-87ab3149a280

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
    (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
        (fun _ => (1 : Field)) = 0 := by
  classical
  ext edge
  unfold qDoubleCylinderBoundary1
  rw [wordLinearMapTranspose_graphBoundary_apply]
  exact ZModModule.add_self 1
end QEC.Coding.BDL26ReplacementCochainMaps
