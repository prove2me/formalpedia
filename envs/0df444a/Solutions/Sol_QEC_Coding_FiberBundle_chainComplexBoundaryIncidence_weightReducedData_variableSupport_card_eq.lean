-- Prove2me | solution 1 for QEC.Coding.FiberBundle.chainComplexBoundaryIncidence_weightReducedData_variableSupport_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:47:18.560971+00:00
-- url     : https://prove2.me/submissions/cc34944b-24f3-4515-862a-267e8add40c6

import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Theorems.Thm_QEC_Coding_FiberBundle_chainComplexBoundaryIncidence_variableSupport_card_eq_boundary_columns
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_variableSupport_card_eq_boundary_columns


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
      fiberZero fiberOne) :
    ((QEC.QLDPC.chainComplexBoundaryIncidence
      (chainComplex (weightReducedData D))).variableSupport q).card =
      HammingWeight
        (boundary1 (weightReducedData D) (reducedQubitBasisWord D q)) +
      HammingWeight
        (wordLinearMapTranspose (boundary2 (weightReducedData D))
          (reducedQubitBasisWord D q)) := by
  classical
  rw [chainComplexBoundaryIncidence_variableSupport_card_eq_boundary_columns
    (chainComplex (weightReducedData D)) q]
  unfold chainComplex reducedQubitBasisWord
  rfl
end QEC.Coding.FiberBundle
