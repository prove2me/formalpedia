-- Prove2me | solution 1 for QEC.Coding.FiberBundle.homologyDistanceAtLeast_weightReduced_of_forward_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:30:46.765951+00:00
-- url     : https://prove2.me/submissions/deee6de2-7e30-4af9-baea-8a5f6dbbcf5c

import Definitions.Def_QEC_Coding_FiberBundle_WeightReduction
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_HomologyDimension
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Theorems.Thm_QEC_Coding_ThreeTermChainHomotopyEquiv_middleHomologyDistanceAtLeast_of_forward_lipschitz


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
    {d L : Nat}
    (hDistance : HomologyDistanceAtLeast D d)
    (hLipschitz : ∀ z,
      HammingWeight ((weightReductionForwardMap1 D h) z) ≤
        L * HammingWeight z) :
    HomologyDistanceAtLeast (weightReducedData D) (d / L) := by
  exact (weightReductionHomotopyEquiv D h
    ).middleHomologyDistanceAtLeast_of_forward_lipschitz
      hDistance hLipschitz
end QEC.Coding.FiberBundle
