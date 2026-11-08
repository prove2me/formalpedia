-- Prove2me | solution 1 for QEC.Coding.FiberBundle.HammingWeight_transpose_boundary1_weightReducedData_single_le_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:40:35.888298+00:00
-- url     : https://prove2.me/submissions/82b8309d-74d0-4f37-bdf7-1c51e11b5a23

import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_transpose_boundary1_single_le
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_weightReducedData_base_row_le_three

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
    (q : ClassicalWeightReduction.WeightReducedCheck R) (i : fiberZero)
    (hFiber : HammingWeight (fun j => D.fiberBoundary i j) ≤ 2) :
    HammingWeight
        (wordLinearMapTranspose (boundary1 (weightReducedData D))
          (Pi.single (q, i) 1)) ≤ 5 := by
  apply (HammingWeight_transpose_boundary1_single_le
    (weightReducedData D) (B := 3) (F := 2) q i
    (HammingWeight_weightReducedData_base_row_le_three D q) hFiber).trans
  omega
end QEC.Coding.FiberBundle
