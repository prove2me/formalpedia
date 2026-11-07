-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.classicalKernelProjectionWord_mem_kernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:26:25.733457+00:00
-- url     : https://prove2.me/submissions/175cf164-a2c3-48ab-8f56-44738431b83a

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
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
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse D S)
    (a : classicalBit) :
    Matrix.toLin' D.classicalBoundary
      (classicalKernelProjectionWord D S a) = 0 := by
  rw [classicalKernelProjectionWord, map_add]
  have hComp :
      (Matrix.toLin' D.classicalBoundary).comp (Matrix.toLin' S) =
        LinearMap.id := by
    rw [← Matrix.toLin'_mul]
    change D.classicalBoundary * S = 1 at hS
    rw [hS]
    simp
  change Matrix.toLin' D.classicalBoundary (Pi.single a 1) +
    ((Matrix.toLin' D.classicalBoundary).comp (Matrix.toLin' S))
      (Matrix.toLin' D.classicalBoundary (Pi.single a 1)) = 0
  rw [hComp]
  exact ZModModule.add_self _
end QEC.Coding.DistanceBalancing
