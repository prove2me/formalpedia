-- Prove2me | solution 1 for QEC.Coding.FiberBundle.cohomologyDistanceAtLeast_weightReduced_of_inverse_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:30:52.966877+00:00
-- url     : https://prove2.me/submissions/9207e54b-6549-4549-bb3e-ddfb401ba5e4

import Definitions.Def_QEC_Coding_FiberBundle_WeightReduction
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_HomologyDimension
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Theorems.Thm_QEC_Coding_ThreeTermChainHomotopyEquiv_middleCohomologyDistanceAtLeast_of_inverse_transpose_lipschitz


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
    (hDistance : CohomologyDistanceAtLeast D d)
    (hLipschitz : ∀ x,
      HammingWeight
          (wordLinearMapTranspose (weightReductionInverseMap1 D h) x) ≤
        L * HammingWeight x) :
    CohomologyDistanceAtLeast (weightReducedData D) (d / L) := by
  exact (weightReductionHomotopyEquiv D h
    ).middleCohomologyDistanceAtLeast_of_inverse_transpose_lipschitz
      hDistance hLipschitz
end QEC.Coding.FiberBundle
