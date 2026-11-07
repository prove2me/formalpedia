-- Prove2me | solution 1 for QEC.Coding.DistanceBalancingSubsystem.mul_hammingWeight_selectedFunctional_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:40:27.595631+00:00
-- url     : https://prove2.me/submissions/247129c5-9af2-4048-bb85-ad994ee32ca3

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Dimension
import Definitions.Def_QEC_Coding_ChainComplex_Homotopy
import Definitions.Def_QEC_Coding_CSS_Subsystem
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Subsystem
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_DistanceBalancing_HammingWeight_eq_sum_indicator
import Theorems.Thm_QEC_Coding_DistanceBalancing_homologySliceMap_mk
import Theorems.Thm_QEC_Coding_DistanceBalancing_kernelTensorToSlices_tmul
import Theorems.Thm_QEC_Coding_DistanceBalancing_sum_HammingWeight_xOneBitSlice_le
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
    {d : Nat}
    (hSource : SD.DressedZDistanceAtLeast d)
    (z : Word (ZMod 2)
      (DistanceBalancing.QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (DistanceBalancing.chainComplex
      (productData SD Y)).middleCycleCode.carrier)
    (phi : Module.Dual (ZMod 2) LogicalZ) :
    d * HammingWeight
        (classicalWordOfHomologyFunctional (productData SD Y) z hz
          (phi.comp (sourceHomologyProjection SD Y))) ≤
      HammingWeight z := by
  rw [DistanceBalancing.HammingWeight_eq_sum_indicator, Finset.mul_sum]
  apply (Finset.sum_le_sum fun a _ha => ?_).trans
    (DistanceBalancing.sum_HammingWeight_xOneBitSlice_le z)
  by_cases ha : classicalWordOfHomologyFunctional
      (productData SD Y) z hz
        (phi.comp (sourceHomologyProjection SD Y)) a ≠ 0
  · rw [if_pos ha, mul_one]
    apply hSource (xOneBitSlice z a)
      (by
        simpa [productData] using
          xOneBitSlice_mem_middleCycleCode (productData SD Y) z hz a)
    intro hProjected
    apply ha
    change phi (sourceHomologyProjection SD Y
      (sourceHomologySlice (productData SD Y) z hz a)) = 0
    rw [sourceHomologyProjection, LinearMap.comp_apply, sourceHomologySlice,
      ThreeTermChainMap.inducedMiddleHomology_mk, sourceCycleSlice]
    change phi (SD.homologyProjection
      (SD.complex.middleBoundaryInCycles.mkQ
        ⟨xOneBitSlice z a, _⟩)) = 0
    rw [hProjected, map_zero]
  · rw [if_neg ha, mul_zero]
    exact Nat.zero_le _
end QEC.Coding.DistanceBalancingSubsystem
