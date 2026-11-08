-- Prove2me | solution 1 for QEC.Coding.FiberBundle.chainComplexBoundaryIncidence_weightReducedData_variableSupport_le_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:50:11.757418+00:00
-- url     : https://prove2.me/submissions/06cbab9c-b8a8-4462-9268-578cc01ba78b

import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_boundary_columns_weightReducedData_le_five
import Theorems.Thm_QEC_Coding_FiberBundle_chainComplexBoundaryIncidence_weightReducedData_variableSupport_card_eq

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
    (q : QubitIndex
      (ClassicalWeightReduction.WeightReducedCheck R)
      (ClassicalWeightReduction.WeightReducedBit R)
      fiberZero fiberOne)
    (hFiberRow : ∀ i : fiberZero,
      HammingWeight (fun j => D.fiberBoundary i j) ≤ 2)
    (hFiberCol : ∀ j : fiberOne,
      HammingWeight (fun i => D.fiberBoundary i j) ≤ 2) :
    ((QEC.QLDPC.chainComplexBoundaryIncidence
      (chainComplex (weightReducedData D))).variableSupport q).card ≤ 5 := by
  rw [chainComplexBoundaryIncidence_weightReducedData_variableSupport_card_eq D q]
  exact HammingWeight_boundary_columns_weightReducedData_le_five
    D q hFiberRow hFiberCol
end QEC.Coding.FiberBundle
