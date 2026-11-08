-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.HammingWeight_boundary2_weightReduced_randomFiberBundleData_canonical_le_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:44:35.688+00:00
-- url     : https://prove2.me/submissions/a52b3096-9c00-4894-ad76-8ff10d2dbba6

import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_cycleBoundary_col_le_two
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_boundary2_weightReducedData_canonical_le_five

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
    (b : ClassicalWeightReduction.WeightReducedBit
      (baseSupportRelation
        (RandomTwist.fiberBundleData baseSample twistSample)))
    (j : ZMod (ell * ell)) :
    HammingWeight
        (boundary2 (weightReducedData
          (RandomTwist.fiberBundleData baseSample twistSample))
          (canonicalBasisWord (F := ZMod 2) (b, j))) ≤ 5 := by
  apply HammingWeight_boundary2_weightReducedData_canonical_le_five
    (RandomTwist.fiberBundleData baseSample twistSample) b j
  exact HammingWeight_cycleBoundary_col_le_two (ell * ell) j
end QEC.Coding.FiberBundle.RandomBase
