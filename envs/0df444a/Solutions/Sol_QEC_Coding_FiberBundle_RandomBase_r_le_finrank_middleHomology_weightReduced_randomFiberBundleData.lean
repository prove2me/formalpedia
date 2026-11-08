-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.r_le_finrank_middleHomology_weightReduced_randomFiberBundleData
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:42:42.732393+00:00
-- url     : https://prove2.me/submissions/88559953-4693-413e-b0d1-ad18fa3928a3

import Definitions.Def_QEC_Coding_FiberBundle_WeightReduction
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_HomologyDimension
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Theorems.Thm_QEC_Coding_FiberBundle_finrank_middleHomology_weightReduced_eq
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_baseSupport_hasNoIsolatedVertices_of_isFullyGood
import Theorems.Thm_QEC_Coding_FiberBundle_r_le_finrank_middleHomology


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
open QEC.Coding.FiberBundle.RandomBase
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hDelta : 1 ≤ Delta)
    (hGood : IsFullyGood (Delta := Delta) baseSample) :
    r ≤ Module.finrank (ZMod 2)
      (chainComplex
        (weightReducedData
          (RandomTwist.fiberBundleData baseSample twistSample))
        ).middleHomology := by
  let D := RandomTwist.fiberBundleData baseSample twistSample
  calc
    r ≤ Module.finrank (ZMod 2) (chainComplex D).middleHomology :=
      r_le_finrank_middleHomology baseSample twistSample hGood.1.2.1
    _ = Module.finrank (ZMod 2)
        (chainComplex (weightReducedData D)).middleHomology :=
      (finrank_middleHomology_weightReduced_eq D
        (baseSupport_hasNoIsolatedVertices_of_isFullyGood
          baseSample twistSample hDelta hGood)).symm
end QEC.Coding.FiberBundle.RandomBase
