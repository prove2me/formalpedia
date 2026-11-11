-- Prove2me | solution 1 for QEC.Coding.BDL26RXInfluenceBounds.readRegion_iff_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:43:08.722403+00:00
-- url     : https://prove2.me/submissions/9566c642-f0c1-45b1-b380-02f7a7ab1ccb

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds
import Theorems.Thm_QEC_Coding_BDL26RXCoarseInfluence_mem_readRegion
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_rxXiLocalComplex_region_mem_iff


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXInfluenceBounds
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter BDL26RXCoarseInfluence BDL26BoundedValence
open BDL26GraphQuantitativeBounds BDL26RZMap1CoordinateBridge
open MultiscaleDecoder RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2 = 0)
namespace QEC.Coding.BDL26RXInfluenceBounds
theorem _root_.solution (p : FamilyZ S depth i.succ) (z : FamilyZ S depth i.castSucc) :
    p ∈ readRegion S depth i h z ↔
      DirectedGraph.distance (rxData S depth i h).levelGraph.graph
        ((rxData S depth i h).topCenter p) ((rxData S depth i h).coarseCenter z) ≤ 2 := by
  rw [mem_readRegion]
  constructor
  · rintro ⟨v, hv, hp⟩
    have he := (rxXiLocalComplex_region_mem_iff (rxData S depth i h) v p).mp hp
    subst v
    exact (Finset.mem_filter.mp hv).2
  · intro hp
    refine ⟨(rxData S depth i h).topCenter p, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
    · exact (rxXiLocalComplex_region_mem_iff _ _ _).mpr rfl
end QEC.Coding.BDL26RXInfluenceBounds
