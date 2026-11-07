-- Prove2me | solution 1 for QEC.Coding.DistanceBalancingSubsystem.productDressedXDistanceAtLeast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:38:44.237786+00:00
-- url     : https://prove2.me/submissions/609fa933-ca37-48fc-a183-007e17c4653d

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Dimension
import Definitions.Def_QEC_Coding_ChainComplex_Homotopy
import Definitions.Def_QEC_Coding_CSS_Subsystem
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Subsystem
import Theorems.Thm_QEC_Coding_DistanceBalancingSubsystem_exists_ne_zero_coordinate
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_DistanceBalancing_HammingWeight_sourceCochainContraction_le
import Theorems.Thm_QEC_Coding_DistanceBalancing_homologySliceMap_mk
import Theorems.Thm_QEC_Coding_DistanceBalancing_kernelTensorToSlices_tmul
import Theorems.Thm_QEC_Coding_DistanceBalancing_projectedSourceCochain_mem_middleCocycleCode
import Theorems.Thm_QEC_Coding_DistanceBalancing_sum_HammingWeight_xOneBitSlice_le_product
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.ClassicalWeightReduction.boundary_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.originalBoundary_single
attribute [local simp] QEC.Coding.DistanceBalancing.homologySliceMap_mk
attribute [local simp] QEC.Coding.DistanceBalancing.kernelTensorToSlices_tmul
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.DistanceBalancingSubsystem
open QEC.Coding
open QEC.Coding.DistanceBalancing
open scoped TensorProduct
universe u v
variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Nonempty classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable {LogicalZ LogicalX : Type v}
variable [AddCommGroup LogicalZ] [Module (ZMod 2) LogicalZ]
variable [AddCommGroup LogicalX] [Module (ZMod 2) LogicalX]
variable [Module.Finite (ZMod 2) LogicalZ]
variable [Module.Finite (ZMod 2) LogicalX]
variable (SD : SubsystemCSSData xZero xOne xTwo LogicalZ LogicalX)
variable (Y : Word (ZMod 2) classicalBit →ₗ[ZMod 2]
  Word (ZMod 2) classicalCheck)
namespace QEC.Coding.DistanceBalancingSubsystem
theorem _root_.solution
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse (productData SD Y) S)
    {d : Nat}
    (hSource : SD.DressedXDistanceAtLeast d) :
    ProductDressedXDistanceAtLeast SD Y S hS d := by
  intro x hx hSelected
  obtain ⟨a, ha⟩ := exists_ne_zero_coordinate
    (selectedCohomologySlices SD Y S hS x hx) hSelected
  have ha' : SD.cohomologyProjection
      (SD.complex.middleCoboundaryInCocycles.mkQ
        ⟨projectedSourceCochain (productData SD Y) S x a, by
          simpa [productData] using
            projectedSourceCochain_mem_middleCocycleCode
              (productData SD Y) S hS x hx a⟩) ≠ 0 := by
    intro hZero
    apply ha
    change SD.cohomologyProjection
      ((originalToSource SD Y).inducedMiddleCohomology
        ((sourceChainComplex (productData SD Y)).middleCoboundaryInCocycles.mkQ
          ⟨projectedSourceCochain (productData SD Y) S x a, _⟩)) = 0
    rw [ThreeTermChainMap.inducedMiddleCohomology_mk]
    convert hZero using 1
    congr 2
    apply Subtype.ext
    simp [ThreeTermChainMap.mapMiddleCocycle, originalToSource,
      wordLinearMapTranspose_id]
  have hLower := hSource
    (projectedSourceCochain (productData SD Y) S x a)
    (by
      simpa [productData] using
        projectedSourceCochain_mem_middleCocycleCode
          (productData SD Y) S hS x hx a)
    ha'
  have hUpper : HammingWeight
      (projectedSourceCochain (productData SD Y) S x a) ≤
      HammingWeight x := by
    exact (HammingWeight_sourceCochainContraction_le x
      (classicalKernelProjectionWord (productData SD Y) S a)).trans
        (sum_HammingWeight_xOneBitSlice_le_product x)
  exact hLower.trans hUpper
end QEC.Coding.DistanceBalancingSubsystem
