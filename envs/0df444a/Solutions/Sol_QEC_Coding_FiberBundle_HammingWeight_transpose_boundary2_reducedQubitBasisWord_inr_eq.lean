-- Prove2me | solution 1 for QEC.Coding.FiberBundle.HammingWeight_transpose_boundary2_reducedQubitBasisWord_inr_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:38:49.5423+00:00
-- url     : https://prove2.me/submissions/65a0b0ca-695c-4312-8900-66d549cff435

import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_one_fiber_coordinate_eq
import Theorems.Thm_QEC_Coding_FiberBundle_transpose_boundary2_reducedQubitBasisWord

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
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    (a : ClassicalWeightReduction.WeightReducedCheck R) (j : fiberOne) :
    HammingWeight
        (wordLinearMapTranspose (boundary2 (weightReducedData D))
          (reducedQubitBasisWord D (Sum.inr (a, j)))) =
      HammingWeight
        (fun b => (weightReducedData D).baseBoundary a b) := by
  classical
  rw [transpose_boundary2_reducedQubitBasisWord D]
  change HammingWeight
      (fun p : ClassicalWeightReduction.WeightReducedBit R × fiberOne =>
        if j = ((weightReducedData D).connection p.1 a).onOne p.2 then
          (weightReducedData D).baseBoundary a p.1 else 0) = _
  exact HammingWeight_one_fiber_coordinate_eq
    (fun b => (weightReducedData D).baseBoundary a b)
    (fun b => ((weightReducedData D).connection b a).onOne) j
end QEC.Coding.FiberBundle
