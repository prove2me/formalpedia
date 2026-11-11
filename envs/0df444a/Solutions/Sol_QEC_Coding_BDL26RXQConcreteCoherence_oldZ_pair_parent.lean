-- Prove2me | solution 1 for QEC.Coding.BDL26RXQConcreteCoherence.oldZ_pair_parent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T07:40:42.406753+00:00
-- url     : https://prove2.me/submissions/1a3e2f92-6b10-4c3b-b27e-71e248aa751d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_physicalZ_parent
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_topCenter_chart
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
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
private theorem raw_z_owner_parent (P : TannerSquarePresentation) (S : OddScale)
    (r : RX2 P S) (z : P.Z) (hr : rxSyndromeOwner P S r=Vertex.z z) :
    rxParent P S (Vertex.z r)=some (Vertex.z z) := by
  rcases r with (⟨x,f⟩ | ⟨q,e⟩) | ⟨w,c⟩
  · cases hr
  · cases hr
  · have hw : w=z := Vertex.z.inj hr
    subst w
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
theorem _root_.solution (h : i.val%2=0)
    (z : (state S i.val).presentation.Z) (copy : Fin 2) :
    parent S (i.val+1)
      (Vertex.z ((rxData S depth i h).induced.zPairEquiv (z,copy)).val)=some (Vertex.z z) := by
  let p := ((rxData S depth i h).induced.zPairEquiv (z,copy)).val
  let r := (physicalZEquiv S depth i h).symm p
  have hc : vertexEquiv (state S i.val).presentation ((rxData S depth i h).topCenter p)=
      Vertex.z z := congrArg (vertexEquiv (state S i.val).presentation)
        ((rxData S depth i h).topCenter_coarse_pair z copy)
  have hr : rxSyndromeOwner (state S i.val).presentation S r=Vertex.z z := by
    have he := topCenter_chart S depth i h r
    rw [Equiv.apply_symm_apply] at he
    exact he.symm.trans hc
  have hp := physicalZ_parent S depth i h r
  rw [Equiv.apply_symm_apply] at hp
  exact hp.trans (raw_z_owner_parent _ S r z hr)
end QEC.Coding.BDL26RXQConcreteCoherence
