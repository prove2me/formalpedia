-- Prove2me | solution 1 for QEC.Coding.DistanceBalancingSubsystem.balancedKernelSubsystemData_dressedXDistanceAtLeast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:54:42.826435+00:00
-- url     : https://prove2.me/submissions/d1d752c2-af50-47a2-a915-30dedbb9c8bf

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_SubsystemDimension
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_SubsystemKernel
import Theorems.Thm_QEC_Coding_DistanceBalancingSubsystem_kernelCohomologyProjection_dressedXDistanceAtLeast

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
    {d : Nat} (hSource : SD.DressedXDistanceAtLeast d) :
    (balancedKernelSubsystemData SD Y).DressedXDistanceAtLeast d := by
  intro x hx hLogical
  exact kernelCohomologyProjection_dressedXDistanceAtLeast
    SD Y hSource x hx hLogical
end QEC.Coding.DistanceBalancingSubsystem
