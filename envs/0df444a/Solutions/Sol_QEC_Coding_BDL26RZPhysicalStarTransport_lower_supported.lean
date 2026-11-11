-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalStarTransport.lower_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:03:50.016204+00:00
-- url     : https://prove2.me/submissions/9f3ccc64-e438-4791-9984-1b1fcb5fff7d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_localized_blocks
import Theorems.Thm_QEC_Coding_BDL26RZErrorPullback_two_run
import Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_two_run


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
    hammingSupport (lowerError S depth i odd a b) ⊆ Q0 S depth i odd u := by
  obtain ⟨p,hp⟩ := BDL26RZFiniteBlockTransport.two_run S depth i odd (by omega)
    _ _ a b (localized_blocks S depth i odd u a b he)
  exact hp.2.2.2.2.1
end QEC.Coding.BDL26RZPhysicalStarTransport
