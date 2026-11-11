-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalStarTransport.oldX_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T08:36:28.480347+00:00
-- url     : https://prove2.me/submissions/7d79abac-5377-4bf7-9089-cdac25e8035b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_potential_oldX_zero


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
theorem _root_.solution (u : FamilyZ S depth i.succ) (a b : Upper S depth i) (p : Potential S depth i)
    (hp : Pullback S depth i odd (Q0 S depth i odd u) {parentZ S depth i odd u} a b p)
    (x : (Old S depth i).X) (copy : BDL26FiniteTannerSquare.Two) : read0 S depth i odd p (.inr (x,copy))=0 :=
  potential_oldX_zero S depth i odd _ _ p hp.2.2.2.2.2.2.2.2.1 x copy
end QEC.Coding.BDL26RZPhysicalStarTransport
