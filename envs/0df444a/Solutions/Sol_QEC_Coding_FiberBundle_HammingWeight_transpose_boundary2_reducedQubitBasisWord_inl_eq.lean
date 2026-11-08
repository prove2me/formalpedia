-- Prove2me | solution 1 for QEC.Coding.FiberBundle.HammingWeight_transpose_boundary2_reducedQubitBasisWord_inl_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:38:47.976519+00:00
-- url     : https://prove2.me/submissions/51f9f156-e8b1-47db-9e98-c16d8edbaa3c

import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_fixed_base_coordinate_eq
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
    (b : ClassicalWeightReduction.WeightReducedBit R) (i : fiberZero) :
    HammingWeight
        (wordLinearMapTranspose (boundary2 (weightReducedData D))
          (reducedQubitBasisWord D (Sum.inl (b, i)))) =
      HammingWeight (fun j => D.fiberBoundary i j) := by
  classical
  rw [transpose_boundary2_reducedQubitBasisWord D]
  change HammingWeight
      (fun p : ClassicalWeightReduction.WeightReducedBit R × fiberOne =>
        if b = p.1 then D.fiberBoundary i p.2 else 0) = _
  exact HammingWeight_fixed_base_coordinate_eq b
    (fun j => D.fiberBoundary i j)
end QEC.Coding.FiberBundle
