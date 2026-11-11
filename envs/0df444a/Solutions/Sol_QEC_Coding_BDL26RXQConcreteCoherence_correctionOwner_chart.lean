-- Prove2me | solution 1 for QEC.Coding.BDL26RXQConcreteCoherence.correctionOwner_chart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:07:02.075526+00:00
-- url     : https://prove2.me/submissions/9ff86685-8ca1-4ee5-ab36-14e2558aa4c1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxData_coordinates
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary1_canonicalBasis_apply
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
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
private theorem heq_apply_cast {A B C : Type} (h : A=B)
    (f : A → C) (g : B → C) (hf : HEq f g) (x : B) :
    f ((Equiv.cast h.symm) x)=g x := by
  cases h
  cases hf
  rfl
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
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
theorem _root_.solution (h : i.val%2=0)
    (r : RX1 (state S i.val).presentation S) :
    vertexEquiv (state S i.val).presentation
      (correctionOwnerAt S depth i h (rxPhysicalQEquiv S depth i h r)) =
        rxCorrectionOwner (state S i.val).presentation S r := by
  have he := heq_apply_cast
    (congrArg (fun C : ConstructionState => C.presentation.Q) (successor_eq S depth i h))
    (correctionOwnerAt S depth i h)
    (fun p => (vertexEquiv (state S i.val).presentation).symm
      (rxCorrectionOwner (state S i.val).presentation S p))
    (rxData_coordinates S depth i h).2.2.2.2.2.2.2 r
  exact (congrArg (vertexEquiv (state S i.val).presentation) he).trans
    (Equiv.apply_symm_apply _ _)
end QEC.Coding.BDL26RXQConcreteCoherence
