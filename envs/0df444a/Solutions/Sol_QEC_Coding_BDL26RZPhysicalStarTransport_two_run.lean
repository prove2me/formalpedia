-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalStarTransport.two_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:15:16.362723+00:00
-- url     : https://prove2.me/submissions/e42d05a8-901f-4865-bcc2-e25e8d8fcc16

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_parent_computed
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_localized_blocks
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_lower_weight
import Theorems.Thm_QEC_Coding_BDL26RZErrorPullback_two_run
import Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_potential_oldX_zero
import Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_two_run
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


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
theorem _root_.solution (above : 3 ≤ i.val) (u : FamilyZ S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    ∃ p : Potential S depth i,
      Pullback S depth i odd (Q0 S depth i odd u) {parentZ S depth i odd u} a b p ∧
      parent S (i.val+1) (Vertex.z u)=some (Vertex.z (parentZ S depth i odd u)) ∧
      HammingWeight (lowerError S depth i odd a b) ≤ 7 ∧
      (∀ x : (Old S depth i).X, ∀ copy : BDL26FiniteTannerSquare.Two, read0 S depth i odd p (.inr (x,copy))=0) := by
  obtain ⟨p,hp⟩ := BDL26RZFiniteBlockTransport.two_run S depth i odd (by omega)
    _ _ a b (localized_blocks S depth i odd u a b he)
  refine ⟨p,hp,parent_computed S depth i odd u,
    (lower_weight S depth i odd above u a b he).1.trans
      (lower_weight S depth i odd above u a b he).2,?_⟩
  exact potential_oldX_zero S depth i odd _ _ p hp.2.2.2.2.2.2.2.2.1
end QEC.Coding.BDL26RZPhysicalStarTransport
