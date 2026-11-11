-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.rzBlockOwner_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T07:45:36.351548+00:00
-- url     : https://prove2.me/submissions/e1aa66cc-3f4b-4e83-bdf4-494d75fc090f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Steps

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
theorem _root_.solution (h : ¬ i.val % 2 = 0) (p : FamilyZ S depth i.succ) :
    p ∈ (rzData S depth i h).coarseRegion (rzBlockOwner S depth i h p) :=
  Classical.choose_spec ((rzData S depth i h).coarseRegion_cover p)
end QEC.Coding.BDL26HistorySyndromeSensitivity
