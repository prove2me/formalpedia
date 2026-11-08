-- Prove2me | solution 1 for QEC.Coding.FiberBundle.cohomologyDistanceAtLeast_weightReduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:55:02.579477+00:00
-- url     : https://prove2.me/submissions/d1a83191-dc5d-4223-ae58-a96db7b3175c

import Definitions.Def_QEC_Coding_FiberBundle_WeightReduction
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_HomologyDimension
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Theorems.Thm_QEC_Coding_FiberBundle_cohomologyDistanceAtLeast_weightReduced_of_inverse_lipschitz
import Theorems.Thm_QEC_Coding_FiberBundle_weightReductionInverseMap1_transpose_lipschitz

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
    (hCheckDegree : ∀ c : baseZero,
      Fintype.card (ClassicalWeightReduction.CheckNeighbor R c) ≤ L)
    (hDistance : CohomologyDistanceAtLeast D d) :
    CohomologyDistanceAtLeast (weightReducedData D) (d / L) := by
  exact cohomologyDistanceAtLeast_weightReduced_of_inverse_lipschitz
    D h hDistance (weightReductionInverseMap1_transpose_lipschitz
      D h hOne hCheckDegree)
end QEC.Coding.FiberBundle
