-- Prove2me | solution 1 for QEC.Coding.DistanceBalancingSubsystem.balancedSubsystemData_dressedXDistanceAtLeast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:51:28.472183+00:00
-- url     : https://prove2.me/submissions/540dc724-89ce-4fe5-93c9-a7e53d61a7ff

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Subsystem
import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Formula
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_SubsystemDimension
import Theorems.Thm_QEC_Coding_DistanceBalancingSubsystem_productDressedXDistanceAtLeast
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
variable (S : Matrix classicalBit classicalCheck (ZMod 2))
namespace QEC.Coding.DistanceBalancingSubsystem
theorem _root_.solution
    (hS : IsClassicalRightInverse (productData SD Y) S)
    {d : Nat}
    (hSource : SD.DressedXDistanceAtLeast d) :
    (balancedSubsystemData SD Y S hS).DressedXDistanceAtLeast d := by
  intro x hx hLogical
  apply productDressedXDistanceAtLeast SD Y S hS hSource x hx
  intro hSlices
  apply hLogical
  change productCohomologyProjection SD Y S hS
      ((DistanceBalancing.chainComplex
        (productData SD Y)).middleCoboundaryInCocycles.mkQ ⟨x, hx⟩) = 0
  rw [productCohomologyProjection, LinearMap.comp_apply]
  have hMap : selectedCohomologySliceMap SD Y S hS
      ((DistanceBalancing.chainComplex
        (productData SD Y)).middleCoboundaryInCocycles.mkQ ⟨x, hx⟩) = 0 := by
    funext a
    exact congrFun hSlices a
  rw [hMap, map_zero]
end QEC.Coding.DistanceBalancingSubsystem
