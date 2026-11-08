-- Prove2me | solution 1 for QEC.Coding.FiberBundle.homologyDistanceAtLeast_weightReduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:52:08.323138+00:00
-- url     : https://prove2.me/submissions/783885e9-6edc-41ff-a269-f7389142b8f2

import Definitions.Def_QEC_Coding_FiberBundle_WeightReduction
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_HomologyDimension
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Theorems.Thm_QEC_Coding_FiberBundle_homologyDistanceAtLeast_weightReduced_of_forward_lipschitz
import Theorems.Thm_QEC_Coding_FiberBundle_weightReductionForwardMap1_lipschitz

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
open scoped BigOperators
universe u
variable {baseZero baseOne fiberZero fiberOne : Type u}
variable [Fintype baseZero] [DecidableEq baseZero]
variable [Fintype baseOne] [DecidableEq baseOne]
variable [Fintype fiberZero] [DecidableEq fiberZero]
variable [Fintype fiberOne] [DecidableEq fiberOne]
variable (D : Data baseZero baseOne fiberZero fiberOne)
local notation "R" => baseSupportRelation D
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    {d L : Nat} (hOne : 1 ≤ L)
    (hBitDegree : ∀ b : baseOne,
      Fintype.card (ClassicalWeightReduction.BitNeighbor R b) ≤ L)
    (hDistance : HomologyDistanceAtLeast D d) :
    HomologyDistanceAtLeast (weightReducedData D) (d / L) := by
  exact homologyDistanceAtLeast_weightReduced_of_forward_lipschitz
    D h hDistance (weightReductionForwardMap1_lipschitz
      D h hOne hBitDegree)
end QEC.Coding.FiberBundle
