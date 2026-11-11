-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalStarTransport.lower_physicalQ_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:32:02.90013+00:00
-- url     : https://prove2.me/submissions/aeb557b9-681a-4c79-a5fa-39643a06f3cd

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_physicalQ_basis
import Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_lowerError_physical_q_basis
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZPhysicalStarTransport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26ReplacementCochainMaps
open BDL26RZDecoderAdapter BDL26RZErrorPullback MultiscaleDecoder
open RZCoarseGraining RZCoarseGrainingData
open BDL26RZFiniteBlockTransport
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val%2=0)
namespace QEC.Coding.BDL26RZPhysicalStarTransport
theorem _root_.solution (a : Upper S depth i) (q : (Old S depth i).Q)
    (v : QDoubleCylinderVertex (transposePresentation (Old S depth i)) q S) :
    lowerError S depth i odd a (a+canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) (physicalQ S depth i odd q v))=
      canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) q := by
  have h := lowerError_physical_q_basis S depth i odd a q v
  exact (congrArg (fun w : Upper S depth i => lowerError S depth i odd a (a+w))
    (physicalQ_basis S depth i odd q v)).symm.trans h
end QEC.Coding.BDL26RZPhysicalStarTransport
