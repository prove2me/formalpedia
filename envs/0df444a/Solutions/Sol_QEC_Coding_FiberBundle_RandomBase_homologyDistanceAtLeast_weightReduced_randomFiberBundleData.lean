-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.homologyDistanceAtLeast_weightReduced_randomFiberBundleData
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:42:36.449858+00:00
-- url     : https://prove2.me/submissions/372b50b2-5601-4afa-8975-3f17ce8a7aae

import Definitions.Def_QEC_Coding_FiberBundle_WeightReduction
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_HomologyDimension
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Theorems.Thm_QEC_Coding_FiberBundle_homologyDistanceAtLeast_weightReduced
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_baseSupportRelation_randomFiberBundleData_iff
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_baseSupport_hasNoIsolatedVertices_of_isFullyGood
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_bitNeighbor_card_le_of_degreeWindows
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
    (hDistance : HomologyDistanceAtLeast
      (RandomTwist.fiberBundleData baseSample twistSample) d) :
    HomologyDistanceAtLeast
      (weightReducedData
        (RandomTwist.fiberBundleData baseSample twistSample))
      (d / (101 * Delta)) := by
  let D := RandomTwist.fiberBundleData baseSample twistSample
  apply homologyDistanceAtLeast_weightReduced D
    (baseSupport_hasNoIsolatedVertices_of_isFullyGood
      baseSample twistSample hDelta hGood)
  · omega
  · intro b
    have hp :
        (fun c => baseSupportRelation D c b) =
          fun c => incidenceRelation baseSample c b := by
      funext c
      exact propext
        (baseSupportRelation_randomFiberBundleData_iff
          baseSample twistSample c b)
    rw [Fintype.card_congr (Equiv.subtypeEquivProp hp)]
    exact bitNeighbor_card_le_of_degreeWindows
      baseSample hGood.1.1 b
  · exact hDistance
end QEC.Coding.FiberBundle.RandomBase
