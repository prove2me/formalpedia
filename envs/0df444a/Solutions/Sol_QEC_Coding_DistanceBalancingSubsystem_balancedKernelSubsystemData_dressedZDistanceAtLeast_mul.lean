-- Prove2me | solution 1 for QEC.Coding.DistanceBalancingSubsystem.balancedKernelSubsystemData_dressedZDistanceAtLeast_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:51:31.241895+00:00
-- url     : https://prove2.me/submissions/23847534-c5e4-4274-a78d-ab27edf35636

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_SubsystemDimension
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_SubsystemKernel
import Theorems.Thm_QEC_Coding_DistanceBalancingSubsystem_productDressedZDistanceAtLeast_mul
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply



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
    {dSource dClassical : Nat}
    (hSource : SD.DressedZDistanceAtLeast dSource)
    (hClassical : ClassicalDistanceAtLeast
      (productData SD Y).classicalBoundary dClassical) :
    (balancedKernelSubsystemData SD Y).DressedZDistanceAtLeast
      (dClassical * dSource) := by
  intro z hz hLogical
  apply productDressedZDistanceAtLeast_mul SD Y hSource hClassical z hz
  intro hSlices
  apply hLogical
  change productHomologyProjection SD Y
      ((DistanceBalancing.chainComplex
        (productData SD Y)).middleBoundaryInCycles.mkQ ⟨z, hz⟩) = 0
  rw [productHomologyProjection, LinearMap.comp_apply]
  have hMap : selectedHomologySliceMap SD Y
      ((DistanceBalancing.chainComplex
        (productData SD Y)).middleBoundaryInCycles.mkQ ⟨z, hz⟩) = 0 := by
    funext a
    change sourceHomologyProjection SD Y
        (sourceHomologySlice (productData SD Y) z hz a) = 0
    exact congrFun hSlices a
  rw [hMap, map_zero]
end QEC.Coding.DistanceBalancingSubsystem
