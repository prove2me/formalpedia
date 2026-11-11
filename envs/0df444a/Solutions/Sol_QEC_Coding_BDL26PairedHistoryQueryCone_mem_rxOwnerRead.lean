-- Prove2me | solution 1 for QEC.Coding.BDL26PairedHistoryQueryCone.mem_rxOwnerRead
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T08:00:47.54201+00:00
-- url     : https://prove2.me/submissions/3c7427d3-02e5-4be5-a996-940aeba3694d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_LocalReads
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_rxXiLocalComplex_region_mem_iff


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26RXCoarseInfluence
open BDL26RXInfluenceBounds BDL26GraphQuantitativeBounds
open MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26PairedHistoryQueryCone
theorem _root_.solution (h : i.val % 2 = 0) (v : Owners S depth i)
    (p : FamilyZ S depth i.succ) :
    p ∈ rxOwnerRead S depth i h v ↔
      (rxData S depth i h).levelGraph.graph.distance
        ((rxData S depth i h).topCenter p) v ≤ 2 := by
  rw [rxOwnerRead, Finset.mem_biUnion]
  constructor
  · rintro ⟨w,hw,hp⟩
    have he := (rxXiLocalComplex_region_mem_iff (rxData S depth i h) w p).mp hp
    subst w
    exact (Finset.mem_filter.mp hw).2
  · intro hp
    exact ⟨_,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩,
      (rxXiLocalComplex_region_mem_iff _ _ _).mpr rfl⟩
end QEC.Coding.BDL26PairedHistoryQueryCone
