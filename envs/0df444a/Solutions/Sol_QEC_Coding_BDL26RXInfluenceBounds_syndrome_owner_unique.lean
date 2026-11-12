-- Prove2me | solution 1 for QEC.Coding.BDL26RXInfluenceBounds.syndrome_owner_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:43:31.625366+00:00
-- url     : https://prove2.me/submissions/0e80029c-9ccd-4f29-9acb-014c01838f24

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds
import Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_syndrome_owner_iff
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
theorem _root_.solution (p : FamilyZ S depth i.succ) :
    ∃! v, p ∈ (rxXiLocalComplex (rxData S depth i h)).syndromeRegion v := by
  refine ⟨(rxData S depth i h).topCenter p, (syndrome_owner_iff S depth i h p _).mpr rfl, ?_⟩
  intro v hv
  exact ((syndrome_owner_iff S depth i h p v).mp hv).symm
end QEC.Coding.BDL26RXInfluenceBounds
