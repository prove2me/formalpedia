-- Prove2me | solution 1 for QEC.Coding.BDL26UniformRXTail.local_q_translate_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:33:30.382923+00:00
-- url     : https://prove2.me/submissions/6df47342-3d8d-4fa3-8082-cd7cb2d3dea0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_qLocalCoboundary_add_constant


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26UniformRXTail
theorem _root_.solution
    (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (g : Word BDL26Field (QDoubleCylinderVertex P q S)) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) (fun v => g v + 1) =
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) g :=
  qLocalCoboundary_add_constant P q S g 1
end QEC.Coding.BDL26UniformRXTail
