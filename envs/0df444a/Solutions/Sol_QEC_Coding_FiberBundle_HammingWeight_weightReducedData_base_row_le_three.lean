-- Prove2me | solution 1 for QEC.Coding.FiberBundle.HammingWeight_weightReducedData_base_row_le_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:23:00.011937+00:00
-- url     : https://prove2.me/submissions/c5adcba6-86fd-4ce2-b2aa-d51b4beb0fc2

import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_HammingWeight_basisCoboundary_le_three
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_basisBoundary_apply_eq_basisCoboundary_apply


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
    (q : ClassicalWeightReduction.WeightReducedCheck R) :
    HammingWeight
        (fun b => (weightReducedData D).baseBoundary q b) ≤ 3 := by
  classical
  change HammingWeight
      (fun b => ClassicalWeightReduction.basisBoundary
        (F := ZMod 2) R b q) ≤ 3
  have hRow :
      (fun b => ClassicalWeightReduction.basisBoundary
        (F := ZMod 2) R b q) =
        ClassicalWeightReduction.basisCoboundary (F := ZMod 2) R q := by
    ext b
    exact ClassicalWeightReduction.basisBoundary_apply_eq_basisCoboundary_apply
      (F := ZMod 2) R b q
  rw [hRow]
  exact ClassicalWeightReduction.HammingWeight_basisCoboundary_le_three
    (F := ZMod 2) R q
end QEC.Coding.FiberBundle
