-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.HammingWeight_boundary_columns_weightReduced_randomFiberBundleData_le_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:38:31.208892+00:00
-- url     : https://prove2.me/submissions/90403f8d-fa1c-49b5-977e-9cacdccca0db

import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_cycleBoundary_row_le_two
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_cycleBoundary_col_le_two
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_boundary_columns_weightReducedData_le_five

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
open scoped BigOperators
universe u v
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
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (q : QubitIndex
      (ClassicalWeightReduction.WeightReducedCheck
        (baseSupportRelation
          (RandomTwist.fiberBundleData baseSample twistSample)))
      (ClassicalWeightReduction.WeightReducedBit
        (baseSupportRelation
          (RandomTwist.fiberBundleData baseSample twistSample)))
      (ZMod (ell * ell)) (ZMod (ell * ell))) :
    HammingWeight
        (boundary1 (weightReducedData
          (RandomTwist.fiberBundleData baseSample twistSample))
          (reducedQubitBasisWord
            (RandomTwist.fiberBundleData baseSample twistSample) q)) +
      HammingWeight
        (wordLinearMapTranspose
          (boundary2 (weightReducedData
            (RandomTwist.fiberBundleData baseSample twistSample)))
          (reducedQubitBasisWord
            (RandomTwist.fiberBundleData baseSample twistSample) q)) ≤ 5 := by
  apply HammingWeight_boundary_columns_weightReducedData_le_five
    (RandomTwist.fiberBundleData baseSample twistSample) q
  · exact fun i => HammingWeight_cycleBoundary_row_le_two (ell * ell) i
  · exact fun j => HammingWeight_cycleBoundary_col_le_two (ell * ell) j
end QEC.Coding.FiberBundle.RandomBase
