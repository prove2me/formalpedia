-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.sum_classicalBoundary_smul_sourceHomologySlice_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:27:55.864562+00:00
-- url     : https://prove2.me/submissions/aa8c1b3d-0fb8-46da-a16a-d9d231c7380a

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Theorems.Thm_QEC_Coding_DistanceBalancing_boundary1_apply_inr
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.ClassicalWeightReduction.boundary_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.originalBoundary_single
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.DistanceBalancing
universe u
open scoped BigOperators
variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable (D : Data xZero xOne xTwo classicalBit classicalCheck)
namespace QEC.Coding.DistanceBalancing
theorem _root_.solution
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (b : classicalCheck) :
    (∑ a : classicalBit,
      D.classicalBoundary b a • sourceHomologySlice D z hz a) = 0 := by
  change (∑ a : classicalBit,
      (sourceChainComplex D).middleBoundaryInCycles.mkQ
        (D.classicalBoundary b a • sourceCycleSlice D z hz a)) = 0
  rw [← map_sum]
  apply (Submodule.Quotient.mk_eq_zero
    (sourceChainComplex D).middleBoundaryInCycles).2
  have hCoe :
      (↑(∑ a : classicalBit,
          D.classicalBoundary b a • sourceCycleSlice D z hz a) :
        Word (ZMod 2) xOne) =
        ∑ a : classicalBit,
          D.classicalBoundary b a • xOneBitSlice z a := by
    ext x1
    simp [sourceCycleSlice]
  change (↑(∑ a : classicalBit,
      D.classicalBoundary b a • sourceCycleSlice D z hz a) :
        Word (ZMod 2) xOne) ∈
      (sourceChainComplex D).middleBoundaryCode.carrier
  rw [hCoe]
  apply ((sourceChainComplex D).mem_middleBoundaryCode_iff _).2
  refine ⟨xTwoCheckSlice z b, ?_⟩
  ext x1
  have hzZero := ((chainComplex D).mem_middleCycleCode_iff z).1 hz
  change boundary1 D z = 0 at hzZero
  have hAt := congrFun hzZero (Sum.inr (x1, b))
  simp only [Pi.zero_apply] at hAt
  rw [boundary1_apply_inr] at hAt
  have hNeg := eq_neg_of_add_eq_zero_left hAt
  simpa [sourceChainComplex, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct, sourceCycleSlice, xTwoCheckSlice,
    ZModModule.neg_eq_self] using hNeg.symm
end QEC.Coding.DistanceBalancing
