-- Prove2me | solution 1 for QEC.Coding.BDL26RXLocalReplacement.qLocalCoboundary_add_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:28:21.766197+00:00
-- url     : https://prove2.me/submissions/2de89cc6-f5ac-49bd-96cb-1ee02a3d5957

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QLocalWeight
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_qLocalCoboundary_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open scoped BigOperators
namespace QEC.Coding.BDL26RXLocalReplacement
theorem _root_.solution (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (f : Word Field (QDoubleCylinderVertex P q S)) (a : Field) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) (fun v => f v + a) =
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) f := by
  ext edge
  rw [qLocalCoboundary_apply, qLocalCoboundary_apply]
  change (f _ + a) + (f _ + a) = f _ + f _
  rw [add_add_add_comm, ZModModule.add_self, add_zero]
end QEC.Coding.BDL26RXLocalReplacement
