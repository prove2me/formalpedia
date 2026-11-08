-- Prove2me | solution 1 for QEC.Coding.FiberBundle.HammingWeight_weightReducedData_base_col_le_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:23:01.561021+00:00
-- url     : https://prove2.me/submissions/009df8c2-cfde-4c52-891c-ed7472926860

import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_HammingWeight_boundary_single_le_three
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.boundary_single



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
    (b : ClassicalWeightReduction.WeightReducedBit R) :
    HammingWeight
        (fun q => (weightReducedData D).baseBoundary q b) ≤ 3 := by
  change HammingWeight
      (ClassicalWeightReduction.basisBoundary (F := ZMod 2) R b) ≤ 3
  rw [← ClassicalWeightReduction.boundary_single]
  exact ClassicalWeightReduction.HammingWeight_boundary_single_le_three
    (F := ZMod 2) R b
end QEC.Coding.FiberBundle
