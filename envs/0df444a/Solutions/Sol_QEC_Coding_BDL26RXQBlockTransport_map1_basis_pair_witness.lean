-- Prove2me | solution 1 for QEC.Coding.BDL26RXQBlockTransport.map1_basis_pair_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:01:34.383516+00:00
-- url     : https://prove2.me/submissions/419a1042-388e-47cf-b4be-4a9fd191b443

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_selected_image_pair
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_map1_basis_coarse_witness

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXQBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXQBlockTransport
theorem _root_.solution (q : QCoord S i) (a : Upper S depth i) (copy : Fin 2) :
    ((indexedDecoderData S depth).selectedMap i).map2
      (coarseSum S depth i h a
        (a+((indexedDecoderData S depth).selectedMap i).map1 (canonicalBasisWord q))).val
      ((Data S depth i h).induced.zPairEquiv (incidentWitness S i q,copy)).val=1 := by
  rw [selected_image_pair S depth i h q,
    map1_basis_coarse_witness S depth i h q a]
end QEC.Coding.BDL26RXQBlockTransport
