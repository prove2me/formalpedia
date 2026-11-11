-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.rzBlockOwner_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T07:49:44.404097+00:00
-- url     : https://prove2.me/submissions/6aebb4d8-d714-44c6-a2b9-63ce8d49578a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Steps
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_rzBlockOwner_mem

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26RXDecoderAdapter BDL26RZDecoderAdapter
open BDL26RXCoarseInfluence BDL26RXInfluenceBounds MultiscaleDecoder
open RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
theorem _root_.solution (h : ¬ i.val % 2 = 0) (p : FamilyZ S depth i.succ)
    (z : FamilyZ S depth i.castSucc) (hp : p ∈ (rzData S depth i h).coarseRegion z) :
    rzBlockOwner S depth i h p = z := by
  by_contra hn
  exact Finset.disjoint_left.mp ((rzData S depth i h).coarseRegion_disjoint _ _ hn)
    (rzBlockOwner_mem S depth i h p) hp
end QEC.Coding.BDL26HistorySyndromeSensitivity
