-- Prove2me | solution 1 for QEC.Coding.FiberBundle.HammingWeight_boundary2_weightReducedData_single_le_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:40:13.733167+00:00
-- url     : https://prove2.me/submissions/8964a1e2-3d87-4a54-9fea-e4c17e9ddc97

import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_boundary2_single_le
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_weightReducedData_base_col_le_three

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
    (b : ClassicalWeightReduction.WeightReducedBit R) (j : fiberOne)
    (hFiber : HammingWeight (fun i => D.fiberBoundary i j) ≤ 2) :
    HammingWeight
        (boundary2 (weightReducedData D) (Pi.single (b, j) 1)) ≤ 5 := by
  apply (HammingWeight_boundary2_single_le
    (weightReducedData D) (B := 3) (F := 2) b j
    (HammingWeight_weightReducedData_base_col_le_three D b) hFiber).trans
  omega
end QEC.Coding.FiberBundle
