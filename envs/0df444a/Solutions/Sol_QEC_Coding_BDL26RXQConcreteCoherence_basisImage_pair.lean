-- Prove2me | solution 1 for QEC.Coding.BDL26RXQConcreteCoherence.basisImage_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T07:40:27.770985+00:00
-- url     : https://prove2.me/submissions/5c820381-1f16-4425-8f3d-569c8b78ef8f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Theorems.Thm_QEC_Coding_BDL26IndexedDecoder_selectedMap_eq
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_map2_diagonal
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary1_canonicalBasis_apply
attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1_canonicalBasis_apply


section
noncomputable section
namespace QEC.Coding.BDL26RXQConcreteCoherence
open MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData (cqComponentTotal)
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26DecodingGraph BDL26IndexedDecoder BDL26AlternatingCochain
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXDecoderAdapter
open BDL26RZMap1CoordinateBridge
  (tannerCoboundary0 tannerCoboundary1 tannerCoboundary1_canonicalBasis_apply)
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
private theorem selected_rx (h : i.val%2=0) :
    (indexedDecoderData S depth).selectedMap i=(indexedDecoderData S depth).rxMap i := by
  rw [selectedMap_eq]
  rfl
end QEC.Coding.BDL26RXQConcreteCoherence
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXQConcreteCoherence
open MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData (cqComponentTotal)
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26DecodingGraph BDL26IndexedDecoder BDL26AlternatingCochain
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXDecoderAdapter
open BDL26RZMap1CoordinateBridge
  (tannerCoboundary0 tannerCoboundary1 tannerCoboundary1_canonicalBasis_apply)
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26RXQConcreteCoherence
theorem _root_.solution (h : i.val%2=0) (q : (state S i.val).presentation.Q)
    (z : (state S i.val).presentation.Z) (copy : Fin 2) :
    basisImage S depth i q ((rxData S depth i h).induced.zPairEquiv (z,copy)).val =
      if (state S i.val).presentation.qz q z=true then 1 else 0 := by
  rw [basisImage,selected_rx S depth i h,(rxData S depth i h).induced.map2_diagonal,
    indexedFamily_coboundary1,tannerCoboundary1_canonicalBasis_apply]
  rfl
end QEC.Coding.BDL26RXQConcreteCoherence
