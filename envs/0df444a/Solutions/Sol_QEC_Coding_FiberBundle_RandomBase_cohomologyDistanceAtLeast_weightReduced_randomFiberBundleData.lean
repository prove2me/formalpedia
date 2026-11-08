-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.cohomologyDistanceAtLeast_weightReduced_randomFiberBundleData
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:42:40.847178+00:00
-- url     : https://prove2.me/submissions/aacde023-4439-452b-a407-4d59d5ed3272

import Definitions.Def_QEC_Coding_FiberBundle_WeightReduction
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_HomologyDimension
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Theorems.Thm_QEC_Coding_FiberBundle_cohomologyDistanceAtLeast_weightReduced
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_baseSupportRelation_randomFiberBundleData_iff
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_baseSupport_hasNoIsolatedVertices_of_isFullyGood
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_checkNeighbor_card_le_of_degreeWindows
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.baseSupportRelation_randomFiberBundleData_iff



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
    {r typeCount ell Delta d : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hDelta : 1 ≤ Delta)
    (hGood : IsFullyGood (Delta := Delta) baseSample)
    (hDistance : CohomologyDistanceAtLeast
      (RandomTwist.fiberBundleData baseSample twistSample) d) :
    CohomologyDistanceAtLeast
      (weightReducedData
        (RandomTwist.fiberBundleData baseSample twistSample))
      (d / (101 * Delta)) := by
  let D := RandomTwist.fiberBundleData baseSample twistSample
  apply cohomologyDistanceAtLeast_weightReduced D
    (baseSupport_hasNoIsolatedVertices_of_isFullyGood
      baseSample twistSample hDelta hGood)
  · omega
  · intro c
    have hp :
        (fun b => baseSupportRelation D c b) =
          fun b => incidenceRelation baseSample c b := by
      funext b
      exact propext
        (baseSupportRelation_randomFiberBundleData_iff
          baseSample twistSample c b)
    rw [Fintype.card_congr (Equiv.subtypeEquivProp hp)]
    exact checkNeighbor_card_le_of_degreeWindows
      baseSample hGood.1.1 c
  · exact hDistance
end QEC.Coding.FiberBundle.RandomBase
