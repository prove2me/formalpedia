-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.homologySliceMap_tensorHomologyMap_tmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:39:29.819105+00:00
-- url     : https://prove2.me/submissions/c134a134-5990-4498-855c-ee702f13d402

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Dimension
import Theorems.Thm_QEC_Coding_DistanceBalancing_sourceCycleSection_spec
import Theorems.Thm_QEC_Coding_DistanceBalancing_homologySliceMap_mk
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


attribute [local simp] QEC.Coding.DistanceBalancing.homologySliceMap_mk

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.DistanceBalancing
universe u
open scoped TensorProduct
variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable (D : Data xZero xOne xTwo classicalBit classicalCheck)
namespace QEC.Coding.DistanceBalancing
theorem _root_.solution
    (h : (sourceChainComplex D).middleHomology)
    (w : ClassicalKernel D) :
    homologySliceMap D (tensorHomologyMap D (h ⊗ₜ[ZMod 2] w)) =
      fun a => w.1 a • h := by
  ext a
  change (sourceChainComplex D).middleBoundaryInCycles.mkQ
      ⟨fun x1 => (sourceCycleSection D h).1 x1 * w.1 a, _⟩ =
    w.1 a • h
  calc
    _ = (sourceChainComplex D).middleBoundaryInCycles.mkQ
        (w.1 a • sourceCycleSection D h) := by
      congr 1
      apply Subtype.ext
      ext x1
      simp [smul_eq_mul, mul_comm]
    _ = w.1 a •
        (sourceChainComplex D).middleBoundaryInCycles.mkQ
          (sourceCycleSection D h) :=
      (sourceChainComplex D).middleBoundaryInCycles.mkQ.map_smul _ _
    _ = w.1 a • h := by rw [sourceCycleSection_spec D h]
end QEC.Coding.DistanceBalancing
